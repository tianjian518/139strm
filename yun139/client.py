# -*- coding: utf-8 -*-
"""
移动云盘（139Yun）API 客户端

严格对照 OpenList drivers/139 实现，支持四种云类型：
  personal_new  新版个人云（默认，推荐）
  personal      旧版个人云
  family        家庭云
  group         群组云
"""

import base64
import logging
import threading
import time
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone

import requests

from . import crypto

logger = logging.getLogger(__name__)

# 当前线程的云盘接口总时限（见 Yun139Client.set_deadline）。
# 用 thread-local 而不是实例属性：client 是按账号缓存、多线程共用的，
# 把时限挂在实例上会被别的请求串改。
_deadline = threading.local()
# 当前线程「跟云盘打了几个来回、共花了多久」。给播放诊断用 ——
# 服务器在海外时，一次播放慢不慢几乎完全由"打了几个来回"决定，
# 所以这个数字比总耗时更能说明问题。
_counters = threading.local()


def count_reset():
    _counters.n = 0
    _counters.ms = 0


def count_snapshot():
    """返回 (来回次数, 合计毫秒)。"""
    return getattr(_counters, "n", 0), getattr(_counters, "ms", 0)


def count_add(ms):
    """手工记一笔。

    探测直链走的是**独立的连接池**（不经过 client 的请求守卫），
    所以它那一次往返不会自动计入。不补上的话，诊断里
    「总耗时 - 来回耗时」会凭空多出一大截，看着像是本地处理很慢，
    其实全是探测 —— 那会把排查带偏。
    """
    try:
        _counters.n = getattr(_counters, "n", 0) + 1
        _counters.ms = getattr(_counters, "ms", 0) + int(ms)
    except Exception:
        pass


def set_request_deadline(seconds):
    """给当前线程设一个云盘接口总时限（秒）；0 = 不限制。

    给调用方（播放路由）用的：不必先拿到 client 实例就能设。
    超时后所有云盘接口调用都会快速失败，而不是继续一个个挂下去。
    """
    _deadline.until = (time.time() + seconds) if seconds else 0


def clear_request_deadline():
    _deadline.until = 0


def _clamp_timeout(timeout, left):
    """把单次调用的超时压到「本次请求还剩下的总时间」以内。

    timeout 可能是 (连接, 读取) 元组，也可能是单个数字。
    连接阶段同样要压：连接慢的时候也是这条线路慢，
    不能连接按 6 秒等、读取再按剩下的时间等，叠起来照样超。
    """
    def clamp(x):
        try:
            x = float(x)
        except Exception:
            return x
        return max(0.2, min(x, left))

    if isinstance(timeout, (tuple, list)):
        return tuple(clamp(t) for t in timeout)
    return clamp(timeout)

CLOUD_TYPES = ("personal_new", "personal", "family", "group")

# 与官方 Web 端保持一致，避免被风控识别为异常客户端
DEVICE_INFO = "||9|7.14.0|chrome|120.0.0.0|||windows 10||zh-CN|||"
YUN_ORIGIN = "https://yun.139.com"

# PC 客户端伪装参数，秒传还原（/file/create）必须使用
PC_APP_VERSION = "8.7.2.20260519"
PC_APP_CHANNEL = "10200153"

CN_TZ = timezone(timedelta(hours=8))


class Yun139Error(Exception):
    """移动云盘接口返回错误。"""


class FileItem:
    """统一的文件/目录模型。"""

    __slots__ = ("file_id", "name", "size", "is_folder", "modified", "path")

    def __init__(self, file_id, name, size=0, is_folder=False, modified=None, path=""):
        self.file_id = file_id
        self.name = name
        self.size = size
        self.is_folder = is_folder
        self.modified = modified
        self.path = path

    def to_dict(self):
        return {
            "file_id": self.file_id,
            "name": self.name,
            "size": self.size,
            "is_folder": self.is_folder,
            "modified": self.modified.isoformat() if self.modified else None,
            "path": self.path,
        }

    def __repr__(self):
        kind = "DIR " if self.is_folder else "FILE"
        return f"<{kind} {self.name} ({self.file_id})>"


class Yun139Client:
    def __init__(self, authorization="", cloud_type="personal_new",
                 mail_cookies="", username="", cloud_id="", timeout=(6, 12)):
        """timeout 默认 (连接 6 秒, 读取 12 秒)。

        【v2.2.23 重要修复】以前这里是 30 —— 单次接口调用最多能挂 30 秒。
        而一次冷启动续播要跟云盘打 9 个来回，只要有两次撞上线路抖动，
        用户就要干等 60 秒以上，播放器全程转圈（用户原话：「加载 1 分钟
        都不播放」）。国内本地部署感觉不到，海外服务器（甲骨文）跨国际
        线路访问国内接口时非常常见。
        现在压到 (6, 12)：单次最多 12 秒，配合下面的请求总时限，
        最坏情况也只是「等十几秒后失败重试」，绝不会无限期转圈。
        """
        if cloud_type not in CLOUD_TYPES:
            raise Yun139Error(f"不支持的云类型: {cloud_type}，可选 {CLOUD_TYPES}")
        self.authorization = (authorization or "").strip()
        self.cloud_type = cloud_type
        self.mail_cookies = mail_cookies
        self.username = username
        self.cloud_id = cloud_id
        self.timeout = timeout

        self.account = ""
        self.personal_host = ""
        self.group_host = ""
        self.family_host = ""
        self.root_folder_id = "/" if cloud_type == "personal_new" else "root"

        self._session = requests.Session()
        self._install_deadline_guard()

    # ------------------------------------------------------------------
    # 请求总时限
    # ------------------------------------------------------------------
    #
    # 单次超时只能管住「一次调用」，管不住「一串调用叠起来」。一次冷启动
    # 续播要串行打 9 个来回，每个最多 12 秒 —— 叠起来还是能到一分多钟。
    # 所以这里再加一道总闸：调用方给一个总时限，超了就直接快速失败，
    # 让播放器立刻拿到结果去重试（重试时状态已热，秒开），
    # 而不是让用户对着转圈等下去。
    def _install_deadline_guard(self):
        raw_request = self._session.request
        client = self

        def _guarded(method, url, **kw):
            until = getattr(_deadline, "until", 0)
            now = time.time()
            if until and now > until:
                raise Yun139Error(
                    "云盘接口响应太慢，已超过本次播放的等待上限 —— "
                    "请重试（重试会快很多）")
            # 单次调用的超时必须**跟着总时限收缩**。
            #
            # 【v2.2.23 修】原来这里只检查"总时限过了没有"，不收缩单次超时：
            # 总时限还剩 3 秒时发起的那一次调用，照样按默认的 12 秒等着，
            # 于是整个请求实际能拖到 25 + 12 ≈ 37 秒 —— 比承诺的 25 秒更久。
            # 现在把本次超时压到"剩下的总时间"，总时限成了真正的硬上限。
            kw.setdefault("timeout", client.timeout)
            if until:
                left = until - now
                if left < 0.2:
                    left = 0.2
                kw["timeout"] = _clamp_timeout(kw["timeout"], left)
            t0 = time.time()
            try:
                return raw_request(method, url, **kw)
            finally:
                # 记一笔：这次播放一共跟云盘打了几个来回、花了多久
                try:
                    _counters.n = getattr(_counters, "n", 0) + 1
                    _counters.ms = (getattr(_counters, "ms", 0)
                                    + int((time.time() - t0) * 1000))
                except Exception:
                    pass

        self._session.request = _guarded

    def set_deadline(self, seconds):
        """给**当前线程**设一个云盘接口总时限（秒）。0 = 不限制。"""
        set_request_deadline(seconds)

    def clear_deadline(self):
        set_request_deadline(0)

    # ------------------------------------------------------------------
    # 凭据处理
    # ------------------------------------------------------------------

    def _split_authorization(self):
        """把 authorization 解成 (前缀, 账号, 令牌)，并校验基本格式。"""
        if not self.authorization:
            raise Yun139Error("尚未配置 Authorization")
        if self.authorization.lower().startswith("basic "):
            raise Yun139Error(
                "Authorization 不能带 Basic 前缀，请只填写 Basic 后面那串 Base64"
            )
        try:
            decoded = base64.b64decode(self.authorization).decode("utf-8")
        except Exception as exc:
            raise Yun139Error(f"Authorization 不是合法的 Base64: {exc}") from exc
        parts = decoded.split(":")
        if len(parts) < 3:
            raise Yun139Error("Authorization 格式不正确，应为 pc:账号:令牌 的 Base64")
        return parts[0], parts[1], ":".join(parts[2:])

    def get_expire_time(self):
        """返回令牌过期时间（本地时间），无法解析时返回 None。"""
        try:
            _, _, token = self._split_authorization()
            strs = token.split("|")
            if len(strs) < 4:
                return None
            ts = int(strs[3]) / 1000
            return datetime.fromtimestamp(ts, CN_TZ)
        except Exception:
            return None

    def token_remain_ms(self):
        """令牌还剩多少毫秒到期；解析不出来返回 None。

        【v2.2.23】抽出来给"刷新失败要不要判死"用 —— 判断令牌到底能不能用，
        必须**直接看它的过期时间**，不能靠"刷新接口通不通"来推断。
        """
        try:
            _, _, token = self._split_authorization()
            strs = token.split("|")
            if len(strs) < 4:
                return None
            return int(strs[3]) - time.time() * 1000
        except Exception:
            return None

    def refresh_token(self):
        """
        令牌剩余有效期超过 15 天时官方不做刷新；过期前会调用刷新接口续期。
        返回 True 表示凭据发生了更新。

        【v2.2.23 —— 修「令牌莫名失效、过一阵又自己好了」】

        用户实测：界面上报「Authorization 已过期，请重新获取」连续 6 次，
        但把**同一条老令牌**重新填一遍就好了；解码令牌一看，它离到期还有
        15.2 天，压根没过期。

        病根有两处，都在这个函数里：

        一、**刷新接口失败 = 判死。** 甲骨文在海外，刷新接口
            (aas.caiyun.feixin.10086.cn) 走跨国际线路，抖一下就
            raise_for_status 抛异常。而这条链一路抛到播放接口，用户看到
            的就是「已过期」—— 令牌明明还能用 15 天。
            真实原因和报出来的原因完全是两码事，把用户和自己都骗了。
            现在：**刷新失败先看令牌本身还能不能用**。还能用（剩余 > 0）
            就照常放行，只是记一条日志；真过期了才往下走兜底。

        二、**剩 0 秒那一下直接抛错，不给任何补救机会。** 现在改成
            交给上层（app.py 的 _ensure_valid_auth）去走 Cookie 兜底登录，
            那条路走不通才把错误抛出来。
        """
        prefix, account, token = self._split_authorization()
        self.account = account

        strs = token.split("|")
        if len(strs) < 4:
            raise Yun139Error("Authorization 中的令牌格式不正确")
        try:
            expiration = int(strs[3])
        except ValueError as exc:
            raise Yun139Error("令牌中的过期时间无法解析") from exc

        remain = expiration - time.time() * 1000
        if remain > 1000 * 60 * 60 * 24 * 15:
            return False          # 还很新，无需刷新

        # 刷新接口只对"还没到期但快到期"的令牌有意义；已过期时官方也不给刷，
        # 直接抛出去让上层走兜底登录（Cookie / 重新填令牌）。
        if remain < 0:
            raise Yun139Error("Authorization 已过期，请重新获取")

        url = "https://aas.caiyun.feixin.10086.cn:443/tellin/authTokenRefresh.do"
        body = ("<root><token>" + token + "</token><account>" + account +
                "</account><clienttype>656</clienttype></root>")
        # 【v2.2.23】刷新接口的失败**必须和"令牌失效"分开对待** —— 见上面注释。
        try:
            resp = self._session.post(
                url, data=body.encode("utf-8"), timeout=self.timeout,
                headers={"Content-Type": "application/xml"},
            )
            resp.raise_for_status()
            root = ET.fromstring(resp.text)
            ret = root.findtext("return")
            if ret != "0":
                desc = root.findtext("desc") or "未知错误"
                raise Yun139Error(f"刷新令牌失败: {desc}")
            new_token = root.findtext("token")
            if not new_token:
                raise Yun139Error("刷新令牌响应中缺少 token")
        except Exception as exc:
            # 刷新没成功 —— 但**这不代表令牌不能用了**。
            # 只要它还没到点，就接着用；网络抖动不该演变成"播放失败"。
            left = remain / 1000
            logger.warning(
                "令牌刷新未成功（%s: %s），但令牌本身还剩 %.0f 天，继续使用",
                type(exc).__name__, str(exc)[:120], left / 86400)
            return False
        else:
            self.authorization = base64.b64encode(
                f"{prefix}:{account}:{new_token}".encode("utf-8")
            ).decode("utf-8")
            return True

    # ------------------------------------------------------------------
    # 底层请求
    # ------------------------------------------------------------------

    def _legacy_headers(self, ts, rand_str, sign):
        """旧版接口请求头（对应 Go request）。"""
        return {
            "Accept": "application/json, text/plain, */*",
            "CMS-DEVICE": "default",
            "Authorization": "Basic " + self.authorization,
            "mcloud-channel": "1000101",
            "mcloud-client": "10701",
            "mcloud-sign": f"{ts},{rand_str},{sign}",
            "mcloud-version": "7.14.0",
            "Origin": YUN_ORIGIN,
            "Referer": YUN_ORIGIN + "/w/",
            "x-DeviceInfo": DEVICE_INFO,
            "x-huawei-channelSrc": "10000034",
            "x-inner-ntwk": "2",
            "x-m4c-caller": "PC",
            "x-m4c-src": "10002",
            "x-SvcType": "2" if self.cloud_type == "family" else "1",
            "Inner-Hcy-Router-Https": "1",
            "Content-Type": "application/json",
        }

    def _new_headers(self, ts, rand_str, sign):
        """新版接口请求头（对应 Go newRequest）。"""
        return {
            "Accept": "application/json, text/plain, */*",
            "Authorization": "Basic " + self.authorization,
            "Caller": "web",
            "Cms-Device": "default",
            "Mcloud-Channel": "1000101",
            "Mcloud-Client": "10701",
            "Mcloud-Route": "001",
            "Mcloud-Sign": f"{ts},{rand_str},{sign}",
            "Mcloud-Version": "7.14.0",
            "x-DeviceInfo": DEVICE_INFO,
            "x-huawei-channelSrc": "10000034",
            "x-inner-ntwk": "2",
            "x-m4c-caller": "PC",
            "x-m4c-src": "10002",
            "x-SvcType": "2" if self.cloud_type == "family" else "1",
            "X-Yun-Api-Version": "v1",
            "X-Yun-App-Channel": "10000034",
            "X-Yun-Channel-Source": "10000034",
            "X-Yun-Client-Info": DEVICE_INFO + "dW5kZWZpbmVk||",
            "X-Yun-Module-Type": "100",
            "X-Yun-Svc-Type": "1",
            "Content-Type": "application/json",
        }

    def _pc_headers(self, ts, rand_str, sign):
        """
        PC 客户端请求头（对应 Go pcPersonalHeaders）。

        秒传还原必须伪装成 PC 客户端，否则 /file/create 会拒绝秒传。
        """
        device_id = self._pc_device_id()
        device_info = (
            "||11|%s|PC|QkYtMjAyMDAzMTAxNjQ3|%s|| Windows 10 (10.0)"
            "|1920X1040|Q2hpbmVzZSAoU2ltcGxpZmllZCk=|||" % (PC_APP_VERSION, device_id)
        )
        headers = self._new_headers(ts, rand_str, sign)
        headers.update({
            "x-DeviceInfo": device_info,
            "x-huawei-channelSrc": PC_APP_CHANNEL,
            "x-MM-Source": "000",
            "x-yun-api-version": "v1",
            "x-yun-app-channel": PC_APP_CHANNEL,
            "x-yun-client-info": device_info,
            "x-yun-device-id": device_id,
            "x-yun-device-info": device_info,
            "x-yun-market-source": "000",
            "x-yun-module-type": "100",
            "x-yun-op-type": "1",
            "x-yun-svc-type": "1",
            "x-ExpRoute-Code": "routeCode=%s,type=2" % self.account,
        })
        return headers

    def _pc_device_id(self):
        return "OPENLIST" + crypto.md5_hex(self.account.encode("utf-8"))[:16].upper() + "-PC"

    def _post(self, url, data, use_new_headers, extra_headers=None):
        ts = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())
        rand_str = crypto.random_str(16)
        body = _json_dumps(data)
        sign = crypto.cal_sign(body, ts, rand_str)
        if extra_headers is not None:
            headers = extra_headers(ts, rand_str, sign)
        else:
            headers = (self._new_headers if use_new_headers else self._legacy_headers)(
                ts, rand_str, sign
            )
        resp = self._session.post(
            url, data=body.encode("utf-8"), headers=headers, timeout=self.timeout
        )
        resp.raise_for_status()
        result = resp.json()
        if not result.get("success"):
            raise Yun139Error(result.get("message") or f"接口返回失败: {url}")
        return result

    def _personal_post(self, pathname, data):
        self._ensure_hosts()
        return self._post(self.personal_host + pathname, data, use_new_headers=True)

    def _pc_personal_post(self, pathname, data):
        """以 PC 客户端身份调用新版个人云接口（秒传还原专用）。"""
        self._ensure_hosts()
        return self._post(
            self.personal_host + pathname, data,
            use_new_headers=True, extra_headers=self._pc_headers,
        )

    def _yun_post(self, pathname, data):
        return self._post(YUN_ORIGIN + pathname, data, use_new_headers=False)

    def _common_account_info(self):
        return {"account": self.account, "accountType": 1}

    def _new_json(self, data):
        merged = {
            "catalogType": 3,
            "cloudID": self.cloud_id,
            "cloudType": 1,
            "commonAccountInfo": self._common_account_info(),
        }
        merged.update(data)
        return merged

    # ------------------------------------------------------------------
    # 初始化
    # ------------------------------------------------------------------

    def _ensure_hosts(self):
        if not self.personal_host:
            self.init()

    def init(self):
        """校验凭据、必要时刷新令牌，并查询各云的接入地址。"""
        if not self.authorization and self.mail_cookies:
            self.login_with_cookies()
        try:
            self.refresh_token()
        except Yun139Error:
            # 【v2.2.23】令牌真过期了 —— 别直接死，先用 Cookie 兜底重登一次。
            # 以前只有"令牌为空"才走 Cookie 登录，导致一条有值但过期的令牌
            # 是彻底死路（用户只能手动重填）。现在过期也能自愈。
            if not self._relogin_with_cookies():
                raise
            logger.info("令牌已过期，已用邮箱 Cookie 重新登录获取新令牌")

        resp = self._post(
            "https://user-njs.yun.139.com/user/route/qryRoutePolicy",
            {
                "userInfo": {
                    "userType": 1,
                    "accountType": 1,
                    "accountName": self.account,
                },
                "modAddrType": 1,
            },
            use_new_headers=False,
        )
        for item in (resp.get("data") or {}).get("routePolicyList") or []:
            mod = item.get("modName")
            url = item.get("httpsUrl") or ""
            if mod == "personal":
                self.personal_host = url
            elif mod == "group":
                self.group_host = url
            elif mod == "family":
                self.family_host = url

        if not self.personal_host:
            raise Yun139Error("未能获取个人云接入地址，请检查 Authorization 是否有效")
        if self.cloud_type in ("group", "family") and not self.group_host:
            raise Yun139Error("未能获取群组/家庭云接入地址")
        return self

    def _relogin_with_cookies(self):
        """令牌失效时用邮箱 Cookie 重新登录换一条新令牌。

        【v2.2.23】抽出来给 init() 兜底用。没有配 Cookie 时返回 False ——
        调用方据此决定是抛错还是放行，**绝不能因为"没配 Cookie"就崩**。
        """
        if not self.mail_cookies:
            return False
        try:
            self.login_with_cookies()
            return True
        except Exception as exc:
            logger.warning("用邮箱 Cookie 重新登录失败: %s", str(exc)[:160])
            return False

    def login_with_cookies(self):
        """用 139 邮箱 Cookie 免密码换取 Authorization（需含 Os_SSo_Sid 与 RMKEY）。"""
        sid, rmkey = _extract_fast_login_cookies(self.mail_cookies)
        if not sid or not rmkey:
            raise Yun139Error(
                "Cookie 中缺少 Os_SSo_Sid 或 RMKEY，请确认复制的是 mail.10086.cn 的完整 Cookie"
            )
        artifact = self._get_single_token(sid, rmkey)
        self.authorization = self._third_party_login(artifact)
        return self.authorization

    def _get_single_token(self, sid, rmkey):
        url = ("https://smsrebuild1.mail.10086.cn/setting/s"
               f"?func=umc:getArtifact&sid={sid}&cguid={int(time.time() * 1000)}")
        resp = self._session.get(
            url, headers={"Cookie": f"RMKEY={rmkey}"}, timeout=self.timeout
        )
        resp.raise_for_status()
        artifact = ((resp.json().get("var") or {}).get("artifact")) or ""
        if not artifact:
            raise Yun139Error("未能用邮箱 Cookie 换取登录票据，Cookie 可能已失效")
        return artifact

    def _third_party_login(self, dycpwd):
        body = {
            "clientkey_decrypt": "l3TryM&Q+X7@dzwk)qP",
            "clienttype": "886",
            "cpid": "507",
            "dycpwd": dycpwd,
            "extInfo": {"ifOpenAccount": "0"},
            "loginMode": "0",
            "msisdn": self.username,
            "pintype": "13",
            "secinfo": crypto.sha1_hex(f"fetion.com.cn:{dycpwd}").upper(),
            "version": "20250901",
        }
        headers = {
            "hcy-cool-flag": "1",
            "x-huawei-channelSrc": "10246600",
            "x-sdk-channelSrc": "",
            "x-MM-Source": "0",
            "x-UserAgent": "android|23116PN5BC|android15|1.2.6|||1440x3200|10246600",
            "x-DeviceInfo": ("4|127.0.0.1|5|1.2.6|Xiaomi|23116PN5BC||02-00-00-00-00-00"
                             "|android 15|1440x3200|android|||"),
            "Content-Type": "text/plain;charset=UTF-8",
            "Accept-Encoding": "gzip",
            "User-Agent": "okhttp/3.12.2",
        }
        payload = crypto.encrypt_body(body)
        resp = self._session.post(
            "https://user-njs.yun.139.com/user/thirdlogin",
            data=payload.encode("utf-8"), headers=headers, timeout=self.timeout,
        )
        resp.raise_for_status()
        layer1 = crypto.decrypt_response(resp.text)
        import json as _json
        hex_inner = _json.loads(layer1.decode("utf-8")).get("data") or ""
        if not hex_inner:
            raise Yun139Error("登录响应缺少 data 字段")
        key2 = bytes.fromhex(crypto.KEY_HEX_2)
        final_bytes = crypto.aes_ecb_decrypt(bytes.fromhex(hex_inner), key2)
        final = _json.loads(final_bytes.decode("utf-8"))
        auth_token = final.get("authToken")
        if not auth_token:
            raise Yun139Error("登录失败，未能取得 authToken")
        account = final.get("account") or self.username
        return base64.b64encode(f"pc:{account}:{auth_token}".encode("utf-8")).decode("utf-8")

    # ------------------------------------------------------------------
    # 文件列表
    # ------------------------------------------------------------------

    def list_files(self, folder_id=None):
        """列出目录下的文件和子目录（内部自动翻页取全量）。"""
        if folder_id in (None, "", "/"):
            folder_id = self.root_folder_id
        if self.cloud_type == "personal_new":
            return self._personal_list(folder_id)
        if self.cloud_type == "personal":
            return self._legacy_personal_list(folder_id)
        if self.cloud_type == "family":
            return self._family_list(folder_id)
        return self._group_list(folder_id)

    def _personal_list(self, parent_file_id):
        items = []
        cursor = ""
        while True:
            data = {
                "imageThumbnailStyleList": ["Small", "Large"],
                "orderBy": "updated_at",
                "orderDirection": "DESC",
                "pageInfo": {"pageCursor": cursor, "pageSize": 100},
                "parentFileId": parent_file_id,
            }
            resp = self._personal_post("/file/list", data)
            payload = resp.get("data") or {}
            for it in payload.get("items") or []:
                items.append(FileItem(
                    file_id=it.get("fileId") or it.get("id"),
                    name=it.get("name") or "",
                    size=int(it.get("size") or 0),
                    is_folder=(it.get("type") == "folder"),
                    modified=_parse_personal_time(it.get("updatedAt") or it.get("createTime")),
                ))
            cursor = payload.get("nextPageCursor") or ""
            if not cursor:
                break
        return items

    def _legacy_personal_list(self, catalog_id):
        items = []
        start = 0
        limit = 100
        while True:
            data = {
                "catalogID": catalog_id,
                "sortDirection": 1,
                "startNumber": start + 1,
                "endNumber": start + limit,
                "filterType": 0,
                "catalogSortType": 0,
                "contentSortType": 0,
                "commonAccountInfo": self._common_account_info(),
            }
            resp = self._yun_post(
                "/orchestration/personalCloud/catalog/v1.0/getDisk", data)
            result = ((resp.get("data") or {}).get("getDiskResult")) or {}
            for c in result.get("catalogList") or []:
                items.append(FileItem(
                    file_id=c.get("catalogID"), name=c.get("catalogName") or "",
                    is_folder=True, modified=_parse_legacy_time(c.get("updateTime")),
                ))
            for c in result.get("contentList") or []:
                items.append(FileItem(
                    file_id=c.get("contentID"), name=c.get("contentName") or "",
                    size=int(c.get("contentSize") or 0), is_folder=False,
                    modified=_parse_legacy_time(c.get("updateTime")),
                ))
            total = int(result.get("totalCount") or len(items))
            start += limit
            if start >= total:
                break
        return items

    def _family_list(self, catalog_id):
        items = []
        page = 1
        while True:
            data = self._new_json({
                "catalogID": "" if catalog_id in (self.root_folder_id, "/") else catalog_id,
                "contentSortType": 0,
                "pageInfo": {"pageNum": page, "pageSize": 100},
                "sortDirection": 1,
            })
            resp = self._yun_post(
                "/orchestration/familyCloud-rebuild/content/v1.2/queryContentList", data)
            payload = resp.get("data") or {}
            for c in payload.get("cloudCatalogList") or []:
                items.append(FileItem(
                    file_id=c.get("catalogID"), name=c.get("catalogName") or "",
                    is_folder=True, modified=_parse_legacy_time(c.get("lastUpdateTime")),
                ))
            for c in payload.get("cloudContentList") or []:
                items.append(FileItem(
                    file_id=c.get("contentID"), name=c.get("contentName") or "",
                    size=int(c.get("contentSize") or 0), is_folder=False,
                    modified=_parse_legacy_time(c.get("lastUpdateTime")),
                ))
            total = int(payload.get("totalCount") or len(items))
            page += 1
            if (page - 1) * 100 >= total:
                break
        return items

    def _group_list(self, catalog_id):
        items = []
        page = 1
        while True:
            data = self._new_json({
                "groupID": self.cloud_id,
                "catalogID": catalog_id.rstrip("/").split("/")[-1],
                "contentSortType": 0,
                "sortDirection": 1,
                "startNumber": page,
                "endNumber": page + 99,
                "path": "/".join([self.root_folder_id.rstrip("/"), catalog_id.lstrip("/")]),
            })
            resp = self._yun_post(
                "/orchestration/group-rebuild/content/v1.0/queryGroupContentList", data)
            result = ((resp.get("data") or {}).get("getGroupContentResult")) or {}
            for c in result.get("catalogList") or []:
                items.append(FileItem(
                    file_id=c.get("catalogID"), name=c.get("catalogName") or "",
                    is_folder=True, modified=_parse_legacy_time(c.get("updateTime")),
                    path=c.get("path") or "",
                ))
            for c in result.get("contentList") or []:
                items.append(FileItem(
                    file_id=c.get("contentID"), name=c.get("contentName") or "",
                    size=int(c.get("contentSize") or 0), is_folder=False,
                    modified=_parse_legacy_time(c.get("updateTime")),
                    path=c.get("path") or "",
                ))
            total = int(result.get("totalCount") or len(items))
            page += 100
            if page > total:
                break
        return items

    # ------------------------------------------------------------------
    # 直链
    # ------------------------------------------------------------------

    def get_download_url(self, file_id, path=""):
        """获取文件直链，供 302 跳转使用。"""
        if self.cloud_type == "personal_new":
            resp = self._personal_post("/file/getDownloadUrl", {"fileId": file_id})
        elif self.cloud_type == "personal":
            resp = self._yun_post(
                "/orchestration/personalCloud/uploadAndDownload/v1.0/downloadRequest",
                {"appName": "", "contentID": file_id,
                 "commonAccountInfo": self._common_account_info()},
            )
        elif self.cloud_type == "family":
            resp = self._yun_post(
                "/orchestration/familyCloud-rebuild/content/v1.0/getFileDownLoadURL",
                self._new_json({"contentID": file_id, "path": path}),
            )
        else:
            resp = self._yun_post(
                "/orchestration/group-rebuild/groupManage/v1.0/getGroupFileDownLoadURL",
                self._new_json({"contentID": file_id, "groupID": self.cloud_id,
                                "path": path}),
            )
        data = resp.get("data") or {}
        url = data.get("downloadURL") or ""
        if url:
            return url
        cdn_url = data.get("cdnUrl") or ""
        if cdn_url and data.get("cdnSwitch"):
            return cdn_url
        url = data.get("url") or ""
        if not url:
            raise Yun139Error(f"未能获取直链: {resp}")
        return url

    # ------------------------------------------------------------------
    # 文件操作（秒传还原 / 清理临时文件用）
    # ------------------------------------------------------------------

    def personal_list(self, parent_file_id, page_size=100):
        """
        列出指定目录下的直接子项（非递归，自动翻页）。

        新版接口返回 data.items（旧版为 data.fileList），两者都兼容。
        """
        self._ensure_hosts()
        items = []
        cursor = ""
        while True:
            resp = self._personal_post("/file/list", {
                "imageThumbnailStyleList": ["Small", "Large"],
                "orderBy": "updated_at",
                "orderDirection": "DESC",
                "pageInfo": {"pageCursor": cursor, "pageSize": page_size},
                "parentFileId": parent_file_id,
            })
            data = resp.get("data") or {}
            batch = data.get("items")
            if batch is None:
                batch = data.get("fileList") or []
            for f in batch:
                items.append(FileItem(
                    file_id=f.get("fileId") or "",
                    name=f.get("name") or "",
                    size=int(f.get("size") or 0),
                    # 目录也可能是 category=folder / type=folder
                    is_folder=(f.get("type") or f.get("category") or "").lower() == "folder",
                    modified=_parse_personal_time(
                        f.get("updatedAt") or f.get("updateTime") or ""
                    ),
                ))
            cursor = data.get("nextPageCursor") or ""
            if not cursor or len(batch) < page_size:
                break
        return items

    def personal_create(self, payload, use_pc_headers=True):
        """
        调用 /file/create（创建文件/目录，或 SHA256 秒传还原）。

        优先使用 PC 头；失败时自动回退到 Web 头。
        """
        self._ensure_hosts()
        if use_pc_headers:
            try:
                return self._pc_personal_post("/file/create", payload)
            except Exception:
                # 回退到 Web 头再试一次
                pass
        return self._personal_post("/file/create", payload)

    def personal_trash(self, file_ids):
        """移入回收站。"""
        self._ensure_hosts()
        return self._personal_post("/recyclebin/batchTrash", {"fileIds": file_ids})

    def personal_delete(self, file_ids):
        """彻底删除（绕过回收站）。"""
        self._ensure_hosts()
        return self._personal_post("/file/batchDelete", {"fileIds": file_ids})

    def personal_get_link(self, file_id):
        """新版个人云直链，优先返回 cdnUrl。"""
        self._ensure_hosts()
        resp = self._personal_post("/file/getDownloadUrl", {"fileId": file_id})
        data = resp.get("data") or {}
        return data.get("cdnUrl") or data.get("url") or ""


# ----------------------------------------------------------------------
# 辅助函数
# ----------------------------------------------------------------------

def _json_dumps(data):
    """紧凑 JSON，键顺序与 Go map 顺序无关（签名只按内容计算）。"""
    import json
    return json.dumps(data, ensure_ascii=False, separators=(",", ":"))


def _extract_fast_login_cookies(cookie_str):
    sid = rmkey = ""
    for part in (cookie_str or "").split(";"):
        if "=" not in part:
            continue
        k, v = part.split("=", 1)
        k, v = k.strip(), v.strip()
        if k == "Os_SSo_Sid":
            sid = v
        elif k == "RMKEY":
            rmkey = v
    return sid, rmkey


def _parse_legacy_time(t):
    """旧接口时间格式：20060102150405"""
    if not t:
        return None
    try:
        return datetime.strptime(str(t), "%Y%m%d%H%M%S").replace(tzinfo=CN_TZ)
    except (ValueError, TypeError):
        return None


def _parse_personal_time(t):
    """新版接口时间格式：2026-08-30T21:30:00.000+08:00"""
    if not t:
        return None
    try:
        return datetime.fromisoformat(str(t).replace("Z", "+00:00"))
    except (ValueError, TypeError):
        return _parse_legacy_time(t)
