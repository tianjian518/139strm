# -*- coding: utf-8 -*-
"""
CAS（秒传文件）解析与还原播放。

.cas 文件本身只有几百字节，内容是一段 Base64 编码的 JSON，记录着原始文件的
名称、大小、MD5 / SHA256 等特征。真正的数据早已存在云盘服务器里，只是从你的
文件列表里看不到了。

播放 .cas 的原理（对照 OpenList 的 drivers/139/cas.go）：
    1. 下载 .cas 文件内容，Base64 + JSON 解出原始文件信息
    2. 用 SHA256 调用 /file/create 做"秒传"——在临时目录里凭空还原出一个真文件
    3. 取这个临时文件的真实直链，302 给播放器
    4. 延迟删除临时文件，云盘里除了 .cas 之外不留痕迹

全程不消耗真实存储空间，也不产生上传流量。
"""

import base64
import copy
import json
import logging
import os
import random
import re
import threading
import time

from yun139.client import Yun139Error

logger = logging.getLogger("139strm.cas")

# 移动云盘接口报这些字眼时，通常是账号「权益」不足（会员等级 / 容量 / 文件大小限制），
# 与 139Strm 本身无关，代码层面无法绕过，只能升级账号或只还原较小的文件。
ENTITLEMENT_KEYWORDS = (
    "权益", "不足", "超限", "容量", "过大", "entitlement", "quota",
)


def _fmt_size(size):
    """把字节数转成人类可读的大小。"""
    if size >= GB:
        return "%.2f GB" % (size / GB)
    if size >= MB:
        return "%.1f MB" % (size / MB)
    return "%d 字节" % size

# 临时还原目录名，放在个人云根目录
TEMP_DIR_NAME = "139STRM_TEMP"

# 还原出来的临时文件保留多久后删除（秒）
# 不能立刻删：播放器拿到 302 之后才会真正发起带 Range 的请求
DEFAULT_TEMP_TTL = 300

# 一个已还原的临时文件允许被复用多久（秒）。
# v2.2.0 起这是个**幂等窗口**，不再是"复用时代"的入场券：
#   * 90 秒足够覆盖 Emby/播放器的「先探测后播放」两次请求、
#     并发去重、直链假活后的换链重建 —— 这些场景复用旧实体可省一次秒传；
#   * 换链（直链 15 分钟过期后回来取新链）时窗口早已关闭，
#     一律走**全新秒传** —— 这正是 OpenList 魔改版 139cas（openlist-
#     guangyapan-src）被生产验证顺畅的模式：每次播放请求即秒传即取链，
#     零历史状态可依赖，也就没有任何"旧实体出状况"的坑可踩。
# 历史：曾 12 小时（隔夜续播复用旧实体 → 「昨天最后看的部今天早上
# 必卡」）→ 4 小时（v2.1.12）→ 90 秒（v2.2.0）。
#
# 【v2.2.22 修正 —— 用户实测"播到后面突然跳回起播点"】
# 5 分钟太小了。用户看一集电视剧，播到后面时画面**跳回起播点，连跳两三次**，
# 时间点正好是每 5 分钟一次。原因就在这个值：
#
#   播放 0~4 分钟：直链缓存命中，同一条链
#   播放 4~5 分钟：缓存过期、会话还在 → 复用同一个临时文件，只换链
#   播放 5 分钟以后：**会话过期 → 全新秒传出一个新文件，并删掉旧文件**
#
# 而播放器手上还攥着指向**旧文件**的链接 —— 文件一被删，那条请求就失败，
# 播放器的反应就是"退回去重新来"，表现正是「跳回起播点」。
#
# 原来那句「会话寿命(300s) < 临时文件寿命(360s)，会话永远比文件先过期」
# 只保证了"会话不会指向已删文件"，却漏了反方向：**删掉的那个文件，
# 播放器可能还在用**。
#
# 现在放宽到 30 分钟（仍然滑动续期）：连续播放期间每 4 分钟回来换一次链，
# 每次都把寿命往后推，于是整集自始至终只用一个临时文件、一个都不删。
# 安全性不靠时长兜底，靠原有的两道硬校验：复用前查文件真实存在
# （_temp_file_exists），直链交出前验活（见 app._fresh_link_broken）——
# 万一文件真没了（比如被清理线程删了），存在性校验会当场发现并重新还原。
# 停止播放后没人续期，临时文件仍按原来的延迟被清掉，不会堆积。
#
# 【v2.2.23】分界线只在「会话过期就要换文件」这件事上才要命。
# 现在换文件已经不再是任何一条路的默认选择了：
#   * 链快到期   → 只对同一文件重签链，不换文件（app._get_cas_link_inner）；
#   * 探测判坏   → 也只重签链，不换文件；
#   * 会话过期   → 这里，是最后一条还会"换文件"的路。
# 所以 30 分钟这个值现在只承担一个职责：保证"会话过期"不会在正常播放
# 途中的短短几分钟内被撞上。只要播放器每次来换链（哪怕隔十几分钟）都能
# 把窗口续上，整集就始终是同一个文件。真正极端的情况（暂停超过 30 分钟
# 再继续）由 _recent_temp_ids 保护名单兜住旧文件不被清扫。
SESSION_TTL = 30 * 60

# 兼容旧名（外部若有引用）
MAX_SESSION_TTL = SESSION_TTL

# 临时目录 ID 的确认结果缓存多久（秒）。以前每次还原都 list 一次根目录
# 确认目录还在 —— 换集点播这种冷启动路径上每多一次接口往返，
# 播放器就多一分「一直加载中」的超时风险。60 秒内用户恰好删掉
# 临时目录的概率可以忽略；真删了，秒传会失败并触发强制重查（见
# _create_in_temp_dir），不会卡死。
#
# 【v2.2.22】60 秒 → 600 秒。这台服务器可能在海外，每次 list 根目录
# 都要跨国际线路走一趟；而「用户恰好在 10 分钟内删掉临时目录」这种事
# 概率极低，且真发生了也有兜底（秒传失败 → 强制重查重试），不会卡死。
#
# 【v2.2.22】600 秒 → 1800 秒。用户实测一个来回约 1 秒，这一秒不该
# 白花在"确认临时目录还在不在"上。后台保温线程每 240 秒会调一次
# ensure_temp_dir()，到 1800 秒时由**后台**去刷新，用户请求几乎总能
# 命中缓存。安全性同上：真删了有秒传失败的兜底。
DIR_CHECK_INTERVAL = 1800

# .cas 解析结果的落盘缓存放在哪：跟 config.json 放一起。
# 放这里的好处是它跟着「配置卷」走 —— 容器重建、升级镜像都不会丢。
def _cas_cache_path():
    cfg = os.environ.get("CONFIG_PATH") or ""
    if not cfg:
        return ""
    d = os.path.dirname(os.path.abspath(cfg))
    return os.path.join(d, "cas_cache.json") if d else ""

# 「只还原视频」时的白名单。.iso 是蓝光/DVD 原盘，也是正儿八经的
# 视频容器（用户拿 139Strm 存原盘很常见）—— 以前漏了它，导致原盘
# .cas 必须开「还原所有类型」才能播，一旦配置丢失就直接播不了。
VIDEO_EXTS = (
    ".mp4", ".mkv", ".avi", ".mov", ".webm", ".flv", ".ts", ".m2ts",
    ".wmv", ".rmvb", ".m4v", ".mpg", ".mpeg", ".3gp",
    ".iso", ".img", ".vob",
)

# .cas 解析结果缓存多久（秒）与最多缓存多少条
# 取一次 .cas 要两次网络往返（下载地址 + GET 内容），缓存后换链/重播
# 直接省掉这两次 —— 换链是 15 分钟一次，命中率很高。
CAS_PARSE_CACHE_TTL = 6 * 3600
CAS_PARSE_CACHE_MAX = 500

MB = 1024 * 1024
GB = 1024 * MB


class CASError(Exception):
    """CAS 解析或还原失败。"""


class CASInfo:
    """.cas 文件里记录的原始文件信息。"""

    __slots__ = ("provider", "name", "size", "md5", "slice_md5",
                 "sha1", "sha256", "pre_id", "create_time")

    def __init__(self, provider="", name="", size=0, md5="", slice_md5="",
                 sha1="", sha256="", pre_id="", create_time=""):
        self.provider = provider
        self.name = name
        self.size = int(size or 0)
        self.md5 = md5
        self.slice_md5 = slice_md5
        self.sha1 = sha1
        self.sha256 = sha256
        self.pre_id = pre_id
        self.create_time = create_time

    def __repr__(self):
        return f"<CASInfo {self.name} ({self.size} bytes, {self.provider})>"


def is_cas_name(name):
    """文件名是否以 .cas 结尾（不区分大小写）。"""
    return (name or "").lower().endswith(".cas")


def is_video_name(name):
    ext = os.path.splitext(name or "")[1].lower()
    return ext in VIDEO_EXTS


# 临时文件名形如 TEMP_<毫秒>_<随机数>_<片名>；云盘在重名时会自动加 " (1)"
_TEMP_PREFIX_RE = re.compile(r"^TEMP_\d+_\d+_(?P<base>.*)$")
_RENAME_SUFFIX_RE = re.compile(r"\s*\(\d+\)(?=\.[^.]*$|$)")


def temp_base_name(name):
    """把临时文件名还原成原始片名，用于认出同一部片子的各个副本。

    'TEMP_1756..._01357_电影 (1).mkv' -> '电影.mkv'
    '电影.mkv'                        -> '电影.mkv'
    """
    s = (name or "").strip()
    m = _TEMP_PREFIX_RE.match(s)
    if m:
        s = m.group("base")
    return _RENAME_SUFFIX_RE.sub("", s)


def decode(data):
    """Base64 + JSON 解出 CAS 内容。"""
    if isinstance(data, str):
        data = data.encode("utf-8")
    data = data.strip()
    try:
        raw = base64.b64decode(data)
    except Exception as exc:
        raise CASError(f"CAS 内容不是合法 Base64: {exc}") from exc
    try:
        payload = json.loads(raw.decode("utf-8"))
    except Exception as exc:
        raise CASError(f"CAS 内容不是合法 JSON: {exc}") from exc

    if not payload.get("name") or payload.get("size") is None:
        raise CASError("CAS 内容缺少 name / size 字段")
    if not (payload.get("md5") or payload.get("sha256") or payload.get("sha1")):
        raise CASError("CAS 内容缺少任何一种文件校验值")

    provider = (payload.get("provider") or "").lower()
    if provider == "115" and not (payload.get("sha1") and payload.get("preID")):
        raise CASError("115 的 CAS 内容缺少 sha1 / preID")

    return CASInfo(
        provider=provider,
        name=payload.get("name") or "",
        size=int(payload.get("size") or 0),
        md5=payload.get("md5") or "",
        slice_md5=payload.get("sliceMd5") or payload.get("md5") or "",
        sha1=payload.get("sha1") or "",
        sha256=payload.get("sha256") or "",
        pre_id=payload.get("preID") or "",
        create_time=str(payload.get("create_time") or ""),
    )


def derive_restore_name(cas_name, original_name):
    """
    由 .cas 文件名和原始文件名推出还原后的文件名。

    例：cas_name="电影.mp4.cas", original_name="电影.mp4" -> "电影.mp4"
        cas_name="电影.cas",     original_name="电影.mp4" -> "电影.mp4"
    """
    base_name = os.path.splitext(cas_name)[0]
    base_name = os.path.splitext(base_name)[0]
    ext = os.path.splitext(original_name)[1]
    if not base_name:
        base_name = os.path.splitext(original_name)[0]
    return base_name + ext


def resolve_restore_name(cas_name, info):
    """校验并得出还原文件名。"""
    if info is None:
        raise CASError("缺少 CAS 内容")
    if not is_cas_name(cas_name):
        raise CASError(f"文件名 {cas_name!r} 不是 .cas 结尾")
    if not os.path.splitext(cas_name)[0].strip():
        raise CASError(f".cas 文件名 {cas_name!r} 去掉后缀后为空")
    restore_name = derive_restore_name(cas_name, info.name).strip()
    if not restore_name:
        raise CASError(f".cas 文件名 {cas_name!r} 推不出原始文件名")
    if "/" in restore_name or "\\" in restore_name:
        raise CASError(f"还原文件名 {restore_name!r} 含有路径分隔符")
    return restore_name


def _part_size(size):
    """分片大小：超过 30GB 用 512MB，否则 100MB。"""
    if size // GB > 30:
        return 512 * MB
    return 100 * MB


def build_part_infos(size):
    part_size = _part_size(size)
    part = 1
    if size > part_size:
        part = (size + part_size - 1) // part_size
    return [
        {
            "partNumber": i + 1,
            "partSize": min(size - i * part_size, part_size),
            "parallelHashCtx": {"partOffset": i * part_size},
        }
        for i in range(part)
    ]


class CASRestorer:
    """在移动云盘上把 .cas 秒传还原成可播放的真文件。"""

    def __init__(self, client, temp_ttl=DEFAULT_TEMP_TTL,
                 temp_dir_name=TEMP_DIR_NAME, allow_all_ext=False):
        self.client = client
        self.temp_ttl = temp_ttl
        self.temp_dir_name = temp_dir_name
        # True 时任何后缀都还原；False 时只还原视频后缀
        self.allow_all_ext = allow_all_ext
        self._temp_dir_id = None
        self._lock = threading.Lock()
        self._pending = {}
        # 临时文件到期时间表：用独立锁保护，避免和 _lock 互相等待
        self._pending_lock = threading.Lock()
        self._reaper = None
        # 已还原会话：cas 文件 ID -> {"temp_id","name","size","created_at"}
        # 播放中反复请求直链时，只复用这里的临时文件重新取一次直链，
        # 绝不重新秒传还原 —— 否则一部电影会被反复还原出几十 GB。
        self._sessions = {}
        # 最近还原过、但已经被新会话顶替掉的临时文件 ID。
        #
        # 【v2.2.22 修「续播跳回起播点」】清扫临时目录时靠 _active_temp_ids()
        # 判断"谁还在被使用、要绕开谁"，而它读的就是 _sessions ——
        # 一部片子只留一条记录。于是续播时新文件一登记，旧文件的 ID 就被
        # 顶掉、从保护名单上消失，紧接着的清扫把它当"闲置副本"删掉。
        # 而播放器手上还攥着指向那个旧文件的链接 → 它一取数据就失败 →
        # 表现就是用户看到的「续播后跳回起播点」。
        #
        # 这里保留一小段"刚被顶替"的文件 ID（只记 ID 和时刻，不占资源），
        # 让清扫绕开它们。播放器拿到直链后就钉死在上面，它随时可能回来取
        # 数据，所以这些文件必须活到延迟删除真正到期为止。
        self._recent_temp_ids = {}
        self._recent_temp_ttl = 3600      # 记住 1 小时，盖过延迟删除的窗口
        # 后台清扫去重：同一片名同时只跑一个清扫线程
        self._sweeping = set()
        self._sweep_lock = threading.Lock()
        # 临时目录 ID 上次确认的时间（节流，见 DIR_CHECK_INTERVAL）
        self._dir_checked_at = 0.0
        # .cas 解析结果缓存：file_id -> (CASInfo, 时刻)，见 CAS_PARSE_CACHE_TTL
        self._cas_cache = {}
        # 每个 .cas 的解析锁：并发请求只让第一个去读云盘，其余等结果
        self._parse_locks = {}
        # 解析缓存落盘文件（跨重启/隔夜仍然有效），懒加载
        self._cas_cache_file = _cas_cache_path()
        self._cas_cache_loaded = False
        # 会话临时文件存在性校验的结果缓存：temp_id -> (是否存在, 时刻)。
        # 避免并发请求各自 list 一遍临时目录。
        self._exist_cache = {}
        # 每个 cas 文件的还原单飞锁，避免并发请求各还原一份
        self._flight = {}
        self._state_lock = threading.Lock()
        # 删除失败的临时文件重试次数
        self._delete_failures = {}
        self.max_session_ttl = SESSION_TTL

    # ------------------------------------------------------------------
    # 解析（带缓存）
    # ------------------------------------------------------------------

    def parse(self, file_id, cas_name):
        """下载 .cas 文件内容并解析出原始文件信息。

        .cas 只有几百字节，但取它要**两次**网络往返（先取下载地址、
        再 GET 内容），而换链/重播每次都要走一遍还原 —— 缓存解析结果
        能直接省掉这两次往返。同一个 file_id 的 .cas 内容不会变，
        缓存 6 小时安全（换链通常 15 分钟一次）。

        【v2.2.22】缓存改为**落盘**：以前只在内存里，容器一重启或隔夜
        就全没了，续播又要重新付这两次往返 —— 而服务器如果在海外，
        这两次就是好几秒。这两秒是纯浪费，因为它取的东西永远不变。

        【v2.2.22】加**按文件的解析锁**：以前这里是 check-then-act，
        浏览器并发发两条播放请求时两边都查不到缓存、于是**各读一遍云盘**
        —— 又是两次往返白扔。用户诊断里那两条重叠的请求（9.5s + 4.8s），
        第二条本来只该花几百毫秒，结果把第一遍的活又干了一遍。
        """
        self._ensure_cas_cache_loaded()
        with self._state_lock:
            hit = self._cas_cache.get(file_id)
        if hit and time.time() - hit[1] < CAS_PARSE_CACHE_TTL:
            return copy.copy(hit[0])

        with self._parse_lock_for(file_id):
            # 拿到锁再查一次：可能刚才那条并发请求已经读好了
            now = time.time()
            with self._state_lock:
                hit = self._cas_cache.get(file_id)
            if hit and now - hit[1] < CAS_PARSE_CACHE_TTL:
                return copy.copy(hit[0])
            url = self.client.get_download_url(file_id)
            resp = self.client._session.get(url, timeout=self.client.timeout)
            resp.raise_for_status()
            info = decode(resp.content)
            with self._state_lock:
                self._cas_cache[file_id] = (info, now)
                if len(self._cas_cache) > CAS_PARSE_CACHE_MAX:
                    for k in sorted(
                            self._cas_cache,
                            key=lambda x: self._cas_cache[x][1]
                    )[:len(self._cas_cache) // 4]:
                        self._cas_cache.pop(k, None)
        self._save_cas_cache()
        return info

    def _parse_lock_for(self, file_id):
        """取（必要时创建）某个 .cas 的解析锁。"""
        with self._state_lock:
            lk = self._parse_locks.get(file_id)
            if lk is None:
                lk = threading.Lock()
                if len(self._parse_locks) > 500:
                    self._parse_locks.clear()
                self._parse_locks[file_id] = lk
            return lk

    # ------------------------------------------------------------------
    # 解析缓存落盘
    # ------------------------------------------------------------------

    def _ensure_cas_cache_loaded(self):
        """第一次用到时把磁盘上的解析缓存读回来。"""
        if self._cas_cache_loaded:
            return
        self._cas_cache_loaded = True
        path = self._cas_cache_file
        if not path or not os.path.exists(path):
            return
        try:
            with open(path, "r", encoding="utf-8") as fh:
                raw = json.load(fh)
        except Exception as exc:
            logger.info("读取 .cas 解析缓存失败（忽略）: %s", exc)
            return
        now = time.time()
        n = 0
        for fid, item in (raw.get("items") or {}).items():
            try:
                ts = float(item.get("t") or 0)
                if now - ts >= CAS_PARSE_CACHE_TTL:
                    continue
                self._cas_cache[fid] = (
                    CASInfo(**(item.get("info") or {})), ts)
                n += 1
            except Exception:
                continue
        if n:
            logger.info("已从磁盘恢复 %d 条 .cas 解析缓存（省下 %d 次接口往返）",
                        n, n * 2)

    def _save_cas_cache(self):
        """把解析缓存写回磁盘（原子写，失败不影响播放）。"""
        path = self._cas_cache_file
        if not path:
            return
        try:
            with self._state_lock:
                items = {}
                for fid, (info, ts) in self._cas_cache.items():
                    items[fid] = {"t": ts, "info": {
                        k: getattr(info, k) for k in info.__slots__}}
            tmp = path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as fh:
                json.dump({"items": items}, fh, ensure_ascii=False)
            os.replace(tmp, path)
        except Exception as exc:
            logger.info("写入 .cas 解析缓存失败（忽略）: %s", exc)

    # ------------------------------------------------------------------
    # 临时目录
    # ------------------------------------------------------------------

    def _scan_temp_dir(self):
        """在根目录里查找临时文件夹；查询失败会抛异常（区别于「确实没有」）。"""
        for item in self.client.personal_list(self.client.root_folder_id):
            if item.name == self.temp_dir_name and item.is_folder:
                return item.file_id
        return None

    def find_temp_dir(self):
        """在根目录里查找已存在的临时文件夹，找不到或查询失败都返回 None。"""
        try:
            return self._scan_temp_dir()
        except Exception as exc:
            logger.warning("列出根目录失败: %s", exc)
            return None

    def ensure_temp_dir(self):
        """取得（必要时创建）根目录里的临时文件夹。

        每次都会重新确认目录 ID：临时目录可能被用户在云盘里删掉，
        或从回收站恢复后 ID 变了。复用一个失效的 ID 会导致所有 CAS
        播放全部失败，所以必须拿到当前真实存在的目录 ID。
        """
        with self._lock:
            # 刚确认过就直接沿用缓存 ID（节流）：换集点播的等待路径上
            # 省一次 list 往返。目录真被删掉的场景由 _create_in_temp_dir
            # 的「失败后强制重查重试」兜底，不会卡死。
            if (self._temp_dir_id
                    and time.time() - self._dir_checked_at < DIR_CHECK_INTERVAL):
                return self._temp_dir_id
            try:
                found = self._scan_temp_dir()
            except Exception as exc:
                # 只是查不到（网络抖动等），手上有记住的 ID 就先沿用，避免误建新目录
                if self._temp_dir_id:
                    logger.warning("列出根目录失败，沿用已记住的临时目录: %s", exc)
                    return self._temp_dir_id
                raise CASError(f"无法列出云盘根目录: {exc}")

            if found:
                if self._temp_dir_id and found != self._temp_dir_id:
                    logger.warning("临时目录 ID 已变化 %s -> %s，已自动更新",
                                   self._temp_dir_id, found)
                self._temp_dir_id = found
                self._dir_checked_at = time.time()
                return found

            root = self.client.root_folder_id
            resp = self.client.personal_create({
                "parentFileId": root,
                "name": self.temp_dir_name,
                "description": "",
                "type": "folder",
                "fileRenameMode": "force_rename",
            })
            data = resp.get("data") or {}
            file_id = data.get("fileId") or ""
            if not file_id:
                raise CASError(f"创建临时目录失败: {resp}")

            # force_rename 下若已同名，服务端会改名，需要重新查一次拿正确 ID
            if (data.get("fileName") or self.temp_dir_name) != self.temp_dir_name:
                found = self.find_temp_dir()
                if found:
                    self._temp_dir_id = found
                    return found
                raise CASError(
                    f"已存在同名目录 {data.get('fileName')}，且无法定位，"
                    f"请手动删除后重试"
                )

            self._temp_dir_id = file_id
            self._dir_checked_at = time.time()
            logger.info("已创建临时目录 %s (%s)", self.temp_dir_name, file_id)
            return file_id

    def set_temp_dir(self, dir_id):
        """调用方持久化的临时目录 ID，避免服务重启后重复创建。"""
        with self._lock:
            self._temp_dir_id = dir_id or None

    def get_temp_dir(self):
        with self._lock:
            return self._temp_dir_id

    # ------------------------------------------------------------------
    # 秒传还原
    # ------------------------------------------------------------------

    def _create_by_sha256(self, dir_id, name, size, sha256):
        if len(sha256) != 64:
            raise CASError(f"SHA256 长度不正确: {len(sha256)}")
        parts = build_part_infos(size)
        sent = parts[:100]
        payload = {
            "contentHash": sha256,
            "contentHashAlgorithm": "SHA256",
            "contentType": "application/octet-stream",
            "parallelUpload": False,
            "partInfos": sent,
            "size": size,
            "parentFileId": dir_id,
            "name": name,
            "type": "file",
            "fileRenameMode": "auto_rename",
        }
        t0 = time.perf_counter()
        try:
            resp = self.client.personal_create(payload, use_pc_headers=True)
        except Yun139Error as exc:
            msg = str(exc)
            if any(k in msg for k in ENTITLEMENT_KEYWORDS):
                # 移动云盘账号权益（会员等级 / 文件大小上限）不足，代码无法绕过
                raise CASError(
                    "账号秒传权益不足，无法还原大小约 %s 的文件（%s）。"
                    "这是移动云盘账号等级限制，与 139Strm 无关；"
                    "请升级移动云盘会员，或只播放较小的 CAS 文件。" % (_fmt_size(size), msg)
                ) from exc
            raise
        took = time.perf_counter() - t0
        if took > 2 or len(parts) > 100:
            # 分片列表只发前 100 片：文件越大，被截掉的比例越高
            # （>10GB 就开始截）。若秒传慢与截断有关，这条日志会给证据。
            logger.info("秒传耗时 %.2fs（%s，分片 %d/%d%s）",
                        took, _fmt_size(size), len(sent), len(parts),
                        " 已截断" if len(parts) > 100 else "")
        data = resp.get("data") or {}
        if not data.get("exist") and not data.get("rapidUpload") \
                and data.get("partInfos") is not None:
            raise CASError(
                "秒传失败：云端已不存在该文件的源数据，.cas 已失效无法还原"
            )
        file_id = data.get("fileId") or ""
        if not file_id:
            raise CASError(f"秒传还原未返回文件 ID: {resp}")
        return file_id, (data.get("fileName") or name)

    def _create_in_temp_dir(self, temp_name, info):
        """在临时目录里秒传还原；目录 ID 失效（被用户删掉等）时强制重查重试一次。

        ensure_temp_dir 有 60 秒确认节流：目录恰在节流期内被删的话，
        第一次 create 会失败 —— 这里清掉缓存 ID 强制重查再来，不会卡死。
        只对「沿用了超过确认间隔的旧 ID」重查：ID 刚确认过还存在的话，
        create 失败多半是账号权益/秒传源数据这类业务原因，重查无济于事。
        """
        last_exc = None
        for attempt in (1, 2):
            with self._lock:
                stale = (self._temp_dir_id is not None
                         and time.time() - self._dir_checked_at
                         >= DIR_CHECK_INTERVAL)
            dir_id = self.ensure_temp_dir()
            try:
                fid, real_name = self._create_by_sha256(
                    dir_id, temp_name, info.size, info.sha256
                )
                return fid, real_name, dir_id
            except Exception as exc:
                last_exc = exc
                if attempt == 2 or not stale:
                    raise
                with self._lock:
                    self._temp_dir_id = None
                    self._dir_checked_at = 0.0
                logger.warning("秒传失败（%s），临时目录 ID 已超过确认间隔，"
                               "强制重查后重试", exc)
        raise last_exc

    def restore_temp(self, cas_file_id, cas_name):
        """
        把 .cas 还原成临时目录里的一个真文件。

        返回 (直链, 原始大小, 临时文件ID, 云端实际文件名, 原始片名)
        """
        t0 = time.perf_counter()
        info = self.parse(cas_file_id, cas_name)
        preview_name = resolve_restore_name(cas_name, info)

        if not self.allow_all_ext and not is_video_name(preview_name):
            raise CASError(
                f"{preview_name!r} 不是视频文件，已跳过还原"
                "（可在配置里开启「还原所有类型」）"
            )
        if not info.sha256:
            raise CASError("CAS 内容缺少 sha256，无法秒传还原")

        temp_dir = self.ensure_temp_dir()
        t1 = time.perf_counter()
        info.name = preview_name
        temp_name = "TEMP_%d_%05d_%s" % (
            int(time.time() * 1000), random.randint(0, 99999), preview_name
        )
        temp_id, real_name, temp_dir = self._create_in_temp_dir(temp_name, info)
        t2 = time.perf_counter()
        logger.info("已秒传还原 %s -> %s (%s)", cas_name, real_name, temp_id)

        try:
            link = self.client.personal_get_link(temp_id)
        except Exception:
            # 取不到直链就别把刚还原的文件留在云盘里占地方
            self.delete_quietly(temp_id)
            raise
        if not link:
            self.delete_quietly(temp_id)
            raise CASError("还原成功但未能取得直链")
        t3 = time.perf_counter()
        total = t3 - t0
        if total > 2:
            # 分段耗时：点下一集「加载中」好几秒时，这条日志直接指出
            # 是取 .cas 慢、秒传慢还是取直链慢，不用猜。
            logger.info("还原耗时 %.2fs（.cas %.2fs / 秒传 %.2fs / 取链 %.2fs）: %s",
                        total, t1 - t0, t2 - t1, t3 - t2, cas_name)
        # real_name 是云端实际文件名（带 TEMP_ 前缀，可能被服务端改号），
        # preview_name 是原始片名，清扫旧副本时按它来认人
        return link, info.size, temp_id, real_name, preview_name

    # ------------------------------------------------------------------
    # 取直链（复用优先）
    # ------------------------------------------------------------------

    def _flight_lock(self, cas_file_id):
        """取得某个 .cas 的还原单飞锁。"""
        with self._state_lock:
            lock = self._flight.get(cas_file_id)
            if lock is None:
                lock = threading.Lock()
                self._flight[cas_file_id] = lock
            return lock

    def _refresh_link(self, temp_id):
        """对已存在的临时文件重新取一条直链；文件没了返回空串。"""
        try:
            return self.client.personal_get_link(temp_id) or ""
        except Exception as exc:
            logger.info("复用临时文件 %s 取直链失败: %s", temp_id, exc)
            return ""

    def _refresh_link_retry(self, temp_id, attempts=3):
        """【v2.2.25】重签直链 + 重试，把「网络抖动」和「文件真没了」分开。

        为什么必须区分：取直链接口是**一次网络调用**，在海外服务器上
        跨国际线路访问，抖动、超时、502 都很常见。以前只要它抛一次异常
        就当场判定"文件没了"→ 丢弃会话 → 走全新秒传 → **换文件** →
        播放器手上那条链指向的旧文件被顶替 → **跳回起播点**。

        而"取链失败"和"文件不存在"完全是两码事：文件在不在要问云盘
        的文件列表（_temp_file_exists，那才是权威判断），不该由一次
        网络异常来回答。

        所以这里先重试几次（退避 0.4s / 1.2s）；全失败再返回空串，
        交给上层。上层拿到空串**也不立刻换文件**（见 fetch_link），
        而是再单独确认一次文件存在性 —— 确认还在就沿用旧链。

        返回 (直链, 是否确定文件已不存在)。
        """
        self._last_refresh_missing = False
        for i in range(max(1, attempts)):
            link = self._refresh_link(temp_id)
            if link:
                return link, False
            # 重试前先单独确认文件还在不在 —— 这是权威判断，一次就够
            if i == 0 and not self._temp_file_exists(temp_id):
                # 云盘明确说文件没了，重试无意义
                logger.info("临时文件 %s 已不在云盘，判定为确实不存在", temp_id)
                self._last_refresh_missing = True
                return "", True
            if i < attempts - 1:
                time.sleep(0.4 * (3 ** i))     # 0.4s → 1.2s
        # 重试全失败、但文件存在性没被否定 → 是网络问题，不是文件问题
        return "", False

    def refresh_link(self, temp_id):
        """对外：**只换链接、不换文件**。

        【v2.2.22】给"链快到期了，但文件还好好的"这种场合用。
        和"重新秒传"的区别是它不动临时文件 —— 旧副本原地留着，
        播放器手上那条旧链万一还没彻底过期也仍能用，不会当场断掉。
        重签失败（文件被删了）返回空串，调用方再走重新还原。
        """
        return self._refresh_link(temp_id)

    def _session_valid(self, cas_file_id):
        """有没有还能用的已还原会话。"""
        with self._state_lock:
            sess = self._sessions.get(cas_file_id)
            if not sess:
                return None
            if time.time() - sess["created_at"] > self.max_session_ttl:
                # 【v2.2.22 关键】会话过期要丢掉，但**必须把它登记的临时文件
                # 记进保护名单**再丢。否则这个文件从保护名单上消失，紧接着
                # 的清扫（续播会走全新秒传并触发清扫）就把它当"闲置副本"
                # 删掉 —— 而播放器手上还攥着指向它的链接。
                #
                # 这正是「续播跳回起播点」的最后一环：用户退出后隔了 1 小时
                # (> SESSION_TTL=30 分钟)，回来续播 → 进到这里 → 会话连同
                # 保护名单一起被清空 → 旧文件被扫掉 → 播放器的旧链接变死链。
                self._recent_temp_ids[sess["temp_id"]] = time.time()
                self._sessions.pop(cas_file_id, None)
                return None
        return sess

    def _drop_session(self, cas_file_id):
        """丢掉会话，但把它登记的临时文件留在保护名单里。"""
        current = 0
        _active = time.time()
        with self._state_lock:
            sess = self._sessions.pop(cas_file_id, None)
            if sess and sess.get("temp_id"):
                self._recent_temp_ids[sess["temp_id"]] = _active
                current = _active
        return sess

    def _drop_session_hard(self, cas_file_id):
        """彻底丢掉会话（调用方已确认那个临时文件确实不该再被使用）。"""
        with self._state_lock:
            return self._sessions.pop(cas_file_id, None)

    def _drop_session_by_temp_id(self, temp_id):
        """临时文件被删掉后，把引用它的还原会话一并清掉。

        以前清理线程删完文件就把会话留在内存里（会话要 12 小时才过期），
        隔天续播时 _refresh_link 会对着这个已删的 temp_id 去取直链 ——
        取直链接口对不存在的文件照样签发一条 URL，但文件已经不在了。
        播放器拿到死链就一直加载，返回重播才走重建。表现就是
        「播一半退出，隔天继续播放一直加载中，重新播放才正常」。
        """
        with self._state_lock:
            dropped = [k for k, s in self._sessions.items()
                       if s["temp_id"] == temp_id]
            for k in dropped:
                self._sessions.pop(k, None)
        return bool(dropped)

    def _active_temp_ids(self):
        """所有正在被复用、或者**刚被顶替但可能还在播**的临时文件 ID。

        【v2.2.22】光看 _sessions 不够：一部片子只留一条会话，续播换了新
        文件之后，旧文件就从名单上消失、被清扫当闲置删掉 —— 而播放器可能
        还攥着指向它的链接。所以把"刚被顶替"的那一段也一并保护起来。
        """
        now = time.time()
        with self._state_lock:
            ids = {s["temp_id"] for s in self._sessions.values()}
            for tid, at in list(self._recent_temp_ids.items()):
                if now - at > self._recent_temp_ttl:
                    self._recent_temp_ids.pop(tid, None)
                else:
                    ids.add(tid)
            return ids

    def _remember_temp(self, temp_id):
        """记下"这个临时文件刚被新会话顶替"，清扫时绕开它。"""
        if not temp_id:
            return
        now = time.time()
        with self._state_lock:
            self._recent_temp_ids[temp_id] = now
            if len(self._recent_temp_ids) > 500:
                for tid in sorted(self._recent_temp_ids,
                                  key=lambda t: self._recent_temp_ids[t])[:100]:
                    self._recent_temp_ids.pop(tid, None)

    def _gc_sessions(self):
        """丢掉过期会话和没人用的单飞锁，避免长期运行后无限增长。"""
        now = time.time()
        with self._state_lock:
            for key in [k for k, s in self._sessions.items()
                        if now - s["created_at"] > self.max_session_ttl]:
                self._sessions.pop(key, None)
            for key in list(self._flight):
                if key in self._sessions:
                    continue
                if not self._flight[key].locked():
                    self._flight.pop(key, None)

    def _purge_leftovers_async(self, base_name):
        """在后台线程清扫这部片子的旧副本，不阻塞还原返回。

        同一片名同一时刻只跑一个清扫；清扫走的 delete_quietly 自带
        失败重试和「删完清会话」，与同步版行为完全一致。
        """
        if not base_name:
            return
        with self._sweep_lock:
            if base_name in self._sweeping:
                return
            self._sweeping.add(base_name)

        def _work():
            try:
                self._purge_leftovers(base_name)
            except Exception as exc:
                logger.warning("后台清扫 %s 旧副本异常（忽略）: %s", base_name, exc)
            finally:
                with self._sweep_lock:
                    self._sweeping.discard(base_name)

        threading.Thread(target=_work, name="cas-sweep", daemon=True).start()

    def wait_sweeps(self, timeout=5.0):
        """等所有后台清扫结束（测试用）。"""
        deadline = time.time() + timeout
        while time.time() < deadline:
            with self._sweep_lock:
                if not self._sweeping:
                    return True
            real_sleep = getattr(time, "real_sleep", None)
            if real_sleep:
                real_sleep(0.02)
            else:
                time.sleep(0.02)
        with self._sweep_lock:
            return not self._sweeping

    def _purge_leftovers(self, restore_name):
        """
        清掉这部片子残留在临时目录里的其它副本。

        服务重启、进程被杀、上一次删除失败都会留下残骸；
        不清理的话，每播一次就多一份，几部片子就能堆出几十 GB。
        正在使用的会话（_sessions 里登记着的）一律跳过。
        """
        if not restore_name:
            return 0
        try:
            temp_dir = self.ensure_temp_dir()
            items = self.client.personal_list(temp_dir)
        except Exception as exc:
            logger.warning("清扫临时目录失败（忽略）: %s", exc)
            return 0
        keep = self._active_temp_ids()
        removed = 0
        target = temp_base_name(restore_name)
        for item in items:
            if item.is_folder or item.file_id in keep:
                continue
            # 按「去掉 TEMP_ 前缀和 (1) 序号后的片名」认人，
            # 这样云盘自动改过名的副本也能被认出来
            if not target or temp_base_name(item.name) != target:
                continue
            self.cancel_delete(item.file_id)
            if self.delete_quietly(item.file_id):
                removed += 1
        if removed:
            logger.info("清扫临时目录：删除 %d 个 %s 的旧副本", removed, restore_name)
        return removed

    def _temp_file_exists(self, temp_id):
        """临时文件是否**真实存在**于云盘临时目录（权威校验，不依赖 CDN）。

        会话复用前的最后防线：不管临时文件是因为什么消失的（用户在
        云盘 App 里删了、清空临时目录、删除重试最终放弃、清理线程
        删了但会话没跟上……），只要云盘里查不到它，就不能复用会话 ——
        否则取直链接口照样会签发一条指向死文件的链接，播放器拿到就
        一直加载。结果短暂缓存，避免并发请求重复 list。
        """
        now = time.time()
        with self._state_lock:
            cached = self._exist_cache.get(temp_id)
        if cached and now - cached[1] < 30:
            return cached[0]
        try:
            temp_dir = self.ensure_temp_dir()
            items = self.client.personal_list(temp_dir)
        except Exception as exc:
            # 查不了不敢断定：保守沿用会话，交由上层直链探测兜底
            logger.warning("确认临时文件存在性失败（沿用会话）: %s", exc)
            return True
        exists = any(i.file_id == temp_id for i in items)
        with self._state_lock:
            self._exist_cache[temp_id] = (exists, now)
        return exists

    def _reuse_link(self, cas_file_id, cas_name, sess):
        """复用已还原的临时文件重新取一条直链；返回直链或空串。

        调用方（_take_reusable_session）已经确认过临时文件在云盘里真实存在，
        走到这里就一律复用、不再秒传 —— 这是「长时间播放不中断、
        临时目录不堆副本」的关键。

        每次成功复用都把会话寿命往后推（滑动续期）：连续播放时一个临时
        文件可以一直用下去，只在停止播放、没人续期之后才自然过期被清理，
        下次续播再全新秒传。

        【v2.2.25 —— 取链失败不再等同于"文件没了"】
        以前这里是「取链失败 → 丢会话 → 返回空 → 上层换文件」，而取链
        只是一次网络调用，海外服务器上抖一下就会失败。于是"网络抖一下"
        被当成了"文件没了"，直接导致换文件、播放器跳回起播点。

        现在改成：
          * 重试几次（网络抖动多半就好了）；
          * 重试仍失败时，**只有云盘明确说文件不存在**才丢会话；
          * 文件还在（只是取链接口不通）→ **沿用会话**，返回空串让上层
            用别的路（旧链）兜住，绝不因为一次接口抖动就换文件。
        """
        link, missing = self._refresh_link_retry(sess["temp_id"])
        if not link:
            if missing:
                # 云盘的权威判断：文件真没了 → 丢会话，换文件是对的
                logger.info("复用失败且文件确实不存在，丢弃会话: %s", cas_name)
                self._drop_session(cas_file_id)
                return ""
            # 文件还在，只是取链接口不通 → 保留会话（下次还能复用），
            # 返回空串让上层酌情沿用旧链
            logger.warning(
                "复用取链失败但文件仍在云盘，保留会话不换文件: %s", cas_name)
            return ""
        with self._state_lock:
            sess["created_at"] = time.time()      # 滑动续期
            sess["last_link"] = link              # 记下可用链，供接口抖动时兜底
        logger.info("复用临时文件换直链（未重新秒传）: %s", cas_name)
        return link

    def _take_reusable_session(self, cas_file_id, cas_name):
        """取出一个**还能放心复用**的还原会话；不能复用就地作废并返回 None。

        两道前置检查，任何一道不过都丢弃会话、走全新秒传：
          1. 会话未过 TTL（_session_valid）—— TTL 只有 90 秒，
             窗口内的实体是刚秒传出来的，几乎不可能出状况；
          2. 临时文件在云盘里真实存在（_temp_file_exists）。
        （v2.1.13 时代的「删除失败名单」检查已删：删除重试从
        文件创建至少 5 分钟后才可能发生，而会话 90 秒就过期，
        名单命中在数学上不可能，留着的死逻辑只会误导人。）
        """
        sess = self._session_valid(cas_file_id)
        if not sess:
            return None
        if not self._temp_file_exists(sess["temp_id"]):
            # 会话登记的临时文件在云盘里已经不存在（不管什么原因）：
            # 不信任这个会话，丢弃后重新秒传 —— 存在性是云盘侧的权威判断，
            # 比 CDN 探测更硬（CDN 对死文件返回 200 也能兜住）
            logger.info("会话的临时文件已不在云盘，丢弃会话重新还原: %s", cas_name)
            self._drop_session(cas_file_id)
            return None
        return sess

    def fetch_link(self, cas_file_id, cas_name):
        """
        取得 .cas 的播放直链：**能复用就复用**。

        返回 (直链, 大小, 临时文件ID, 还原文件名, 是否重新秒传)。

        播放过程中播放器会反复来换直链，如果每次都重新秒传还原，
        临时目录里就会同时躺着好几份完整电影（旧的要等 TTL 才删），
        一部片子就能堆出几十 GB。这里改成：
          1. 已有还原好的临时文件 → 换一条新直链即可，零新增文件；
          2. 临时文件确实没了 → 才重新秒传，且先清掉这部片子的旧副本。
        """
        sess = self._take_reusable_session(cas_file_id, cas_name)
        if sess:
            link = self._reuse_link(cas_file_id, cas_name, sess)
            if link:
                return link, sess["size"], sess["temp_id"], sess["name"], False

        # 单飞：并发请求只让第一个去还原，其余的等它出结果后直接复用
        with self._flight_lock(cas_file_id):
            sess = self._take_reusable_session(cas_file_id, cas_name)
            if sess:
                link = self._reuse_link(cas_file_id, cas_name, sess)
                if link:
                    return link, sess["size"], sess["temp_id"], sess["name"], False
                # 【v2.2.25 总闸】走到这里 = 复用这条路的两次尝试都没拿到链。
                # 但如果**文件还在云盘里**，那问题出在「取链接口」而不是
                # 「文件」—— 这时候去重新秒传，会用一个新文件顶替掉旧文件，
                # 而播放器手里那条指向旧文件的链当场变死 → **跳回起播点**。
                #
                # 铁律：**只要文件还在，就绝不换文件。**
                #
                # 兜底手段：把这个会话**上一次成功签发的直链**交出去。
                # 那条链多半还没过期（有效期 15 分钟），播放器拿它能接着播；
                # 就算已过期，也比"换文件导致跳回起点"强 —— 前者是一次
                # 重试就能好，后者是实打实的中断。下次请求来时接口恢复了，
                # 自然就走正常复用了。
                if self._temp_file_exists(sess["temp_id"]):
                    stale = sess.get("last_link") or ""
                    logger.warning(
                        "复用取链失败但文件仍在，沿用上次的链不换文件: %s",
                        cas_name)
                    if stale:
                        return (stale, sess["size"], sess["temp_id"],
                                sess["name"], False)
                    raise CASError(
                        "临时文件存在但暂时取不到直链（云盘接口抖动），"
                        "已保留原文件，请稍后重试"
                    )

            link, size, temp_id, real_name, base_name = self.restore_temp(
                cas_file_id, cas_name
            )
            # 先登记会话再清扫：这样新文件会被列入保护名单，不会被自己清掉。
            # 同时把**被顶替掉的旧文件**也记进保护名单 —— 播放器拿到直链后
            # 就钉死在上面了，续播换了新文件不代表它不用旧的了（v2.2.22）。
            #
            # 注意顺序：必须在启动后台清扫**之前**把两件事都做完。清扫是
            # 另一个线程，它读保护名单时如果这边还没登记完，就会把旧文件
            # 当成"闲置副本"删掉 —— 那正是「续播跳回起播点」的成因。
            with self._state_lock:
                old = self._sessions.get(cas_file_id)
                if old and old.get("temp_id") != temp_id:
                    self._recent_temp_ids[old["temp_id"]] = time.time()
                self._sessions[cas_file_id] = {
                    "temp_id": temp_id,
                    "name": real_name,
                    "base_name": base_name,
                    "size": size,
                    "created_at": time.time(),
                    "last_link": link,     # 供"取链接口抖动"时兜底（v2.2.25）
                }
            # 清扫旧副本放后台：点「下一集」这类冷启动请求，
            # 返回前的每次同步接口调用都在给播放器的超时添筹码
            self._purge_leftovers_async(base_name)
            self._gc_sessions()
            logger.info("已秒传还原 %s -> %s（临时文件 %s）",
                        cas_name, real_name, temp_id)
            return link, size, temp_id, real_name, True

    def forget_session(self, cas_file_id):
        """丢掉这个 .cas 的还原会话（直链失效、需要强制重建时用）。"""
        with self._state_lock:
            return self._sessions.pop(cas_file_id, None)

    def session_count(self):
        """当前保持着的还原会话数量。"""
        with self._state_lock:
            return len(self._sessions)

    def has_session(self, cas_file_id):
        """这部 .cas 之前还原过吗（会话还在，或者刚被顶替但还在保护名单里）。

        【v2.2.22】给续播判定当"服务端有没有痕迹"的证据。
        注意这里**不关心会话是否过期**：过期的会话会被 _session_valid
        挪进 _recent_temp_ids（保护名单），那也是"播放器可能还在用它"的
        痕迹，同样算数。
        """
        now = time.time()
        with self._state_lock:
            if cas_file_id in self._sessions:
                return True
            for tid, at in self._recent_temp_ids.items():
                if now - at <= self._recent_temp_ttl:
                    # 保护名单只记 ID、没记它属于哪部片子；
                    # 有存活条目就说明"最近确实还原过东西"，
                    # 这对判定已经够用（真新播时这里是空的）。
                    return True
            return False

    # ------------------------------------------------------------------
    # 清理
    # ------------------------------------------------------------------

    def delete_quietly(self, file_id):
        """先移入回收站、再彻底删除，失败只记日志不抛错。

        只要文件离开了临时目录就算成功（进了回收站也不再堆在临时目录里）。
        """
        trashed = False
        try:
            self.client.personal_trash([file_id])
            trashed = True
        except Exception as exc:
            logger.warning("移入回收站失败 %s: %s", file_id, exc)
        try:
            self.client.personal_delete([file_id])
            logger.info("已清理临时文件 %s", file_id)
            self._drop_session_by_temp_id(file_id)
            with self._state_lock:
                self._delete_failures.pop(file_id, None)
            return True
        except Exception as exc:
            if trashed:
                logger.info("临时文件 %s 已进回收站，彻底删除失败（可忽略）: %s",
                            file_id, exc)
                self._drop_session_by_temp_id(file_id)
                with self._state_lock:
                    self._delete_failures.pop(file_id, None)
                return True
            logger.warning("彻底删除失败 %s: %s", file_id, exc)
            return False

    def cancel_delete(self, file_id):
        """把文件从待删表里摘掉（准备手动删除 / 会话重建时用）。"""
        with self._pending_lock:
            self._pending.pop(file_id, None)
        with self._state_lock:
            self._delete_failures.pop(file_id, None)

    def schedule_delete(self, file_id, delay=None):
        """登记临时文件的延迟删除时间（到点由后台清理线程删掉）。

        对同一个文件重复调用 = **续期**：只推迟删除时间，不会再起新线程。
        旧实现每次调用都新起一个线程，导致续期之后旧线程仍会按时把文件删掉，
        表现就是「播过的视频，过一会儿再播就一直加载」。
        """
        delay = self.temp_ttl if delay is None else delay
        with self._pending_lock:
            self._pending[file_id] = time.time() + delay
        self._ensure_reaper()
        return delay

    def _ensure_reaper(self):
        """保证后台清理线程只起一次。"""
        with self._pending_lock:
            if self._reaper is not None and self._reaper.is_alive():
                return
            self._reaper = threading.Thread(target=self._reap_loop,
                                            name="cas-reaper", daemon=True)
            self._reaper.start()

    def _reap_loop(self):
        """每 10 秒检查一次，删掉到期的临时文件。

        删除失败的文件会退避重试（最多 6 次）。以前失败一次就永久遗忘，
        接口抖一下就会在云盘里留下一份永远清不掉的大文件。
        """
        while True:
            try:
                time.sleep(10)
                now = time.time()
                with self._pending_lock:
                    due = [fid for fid, exp in list(self._pending.items())
                           if exp <= now]
                    for fid in due:
                        self._pending.pop(fid, None)
                for fid in due:
                    if self.delete_quietly(fid):
                        continue
                    give_up = False
                    with self._state_lock:
                        tries = self._delete_failures.get(fid, 0) + 1
                        if tries > 8:
                            self._delete_failures.pop(fid, None)
                            give_up = True
                        else:
                            self._delete_failures[fid] = tries
                    if give_up:
                        # v2.2.0：放弃就是纯放弃。会话只有 90 秒寿命，
                        # 早就自然过期了，不需要（也不应该）在这里作废；
                        # 残骸无害化 —— 没有任何会话会引用它，这部片子
                        # 下次播放必然全新秒传，还原后的同名清扫还会
                        # 再尝试删掉它。
                        logger.error("临时文件 %s 连续 %d 次删除失败，放弃"
                                     "（残骸将留待下次还原时清扫）", fid, tries)
                        continue
                    with self._pending_lock:
                        # 平方退避、30 分钟封顶：夜间接口抖动的恢复窗口
                        # 从原来的 ~20 分钟拉长到 ~2.5 小时，避免一次
                        # 深夜故障就留下永久残骸
                        self._pending[fid] = now + min(60 * tries * tries,
                                                       1800)
            except Exception as exc:
                logger.warning("临时文件清理线程异常: %s", exc)

    def purge_temp_dir(self, max_age=None):
        """
        清空临时目录里所有残留文件。

        max_age 为 None 时无条件清空；否则只清理创建超过指定秒数的。
        返回清理数量。
        """
        try:
            temp_dir = self.ensure_temp_dir()
            items = self.client.personal_list(temp_dir)
        except Exception as exc:
            raise CASError(f"读取临时目录失败: {exc}") from exc
        count = 0
        for item in items:
            if max_age is not None:
                if item.modified is None:
                    continue
                age = time.time() - item.modified.timestamp()
                if age < max_age:
                    continue
            if self.delete_quietly(item.file_id):
                count += 1
        return count

    def pending_count(self):
        """当前等待延迟删除的临时文件数量。"""
        now = time.time()
        with self._pending_lock:
            snapshot = list(self._pending.values())
        return sum(1 for exp in snapshot if exp > now)
