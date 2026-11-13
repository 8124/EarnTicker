# -*- coding: utf-8 -*-
"""
EarnTicker — 托盘实时收入显示器
------------------------------------------------
点击任务栏右下角托盘图标，弹出卡片：
    本月已赚 / 今日已赚 / 秒薪（含实扣口径）/ 喝水时间 / 本日进度
月薪与上下班时段可在面板内直接设置（首次运行默认月薪 1 元，改过之后记住自己的值）。

在岗判定：只看键鼠活跃度。过去 4 分钟内有键鼠动作的秒数占比，按四个档位切换状态
（边界处留 2% 滞回防抖，不来回跳）。四种状态各自折算进「实际工作时长」：
        < 23%         疯狂喝水中  深绿   ×0.1
        23% ~ 50%     喝水中      浅绿   ×0.5
        50% ~ 77%     工作中      黄     ×1.0
        ≥ 77%         埋头工作中  红     ×2.0
    午休 / 上班前 / 下班后 / 非工作日一律「休息中」，不计入任何时长，数字冻结。
    · 秒薪   = 日薪 ÷ 标定班时（固定值）
    · 实扣秒薪 = 今日已赚 ÷ 实际工作时长（实时，即界面上的“实际”小字）
    · 喝水   = 已过计薪时长 − 真正在干活的秒数，摸鱼多久就是多久，不打折
    · 进度条 = 上班到下班的整段钟面（含午休），按每分钟记录的状态分段着色
"""

import ctypes
import json
import os
import queue
import sys
import threading
import time
from collections import deque
from datetime import date, datetime

import tkinter as tk
from tkinter import font as tkfont

from PIL import Image, ImageDraw, ImageFont, ImageTk
import pystray

APP_NAME = "EarnTicker"
EVENT_NAME = "EarnTicker_Show_Event_v2"

FROZEN = bool(getattr(sys, "frozen", False))
if FROZEN:
    # 打包成 exe 后，__file__ 在临时解包目录里；图标放到 %APPDATA%，避免污染桌面
    HERE = os.path.dirname(os.path.abspath(sys.executable))
    ICON_DIR = os.path.join(os.environ.get("APPDATA", HERE), APP_NAME)
else:
    HERE = os.path.dirname(os.path.abspath(__file__))
    ICON_DIR = HERE
ICON_PATH = os.path.join(ICON_DIR, "EarnTicker.ico")

# ---------------------------------------------------------------- 调色板
CARD_TOP = (28, 32, 40)
CARD_BOT = (15, 18, 23)
CARD_BG_HEX = "#0F1217"
BORDER = (54, 61, 74)
TEXT = "#F2F5FA"
MUTED = "#8A93A3"
FAINT = "#6F7889"
GOLD = "#FFC24B"
GOLD_RGB = (255, 194, 75)
TICK_BG = (26, 30, 38)          # 跳字淡出时渐变的底色
INPUT_BG = (36, 41, 51)
GHOST_BG = (33, 38, 47)
GHOST_HOVER = (44, 50, 62)

# 六种状态：进度条分段与右上角胶囊共用同一套色
ST_REST = 0        # 休息中     —— 进度条不上色，胶囊点用灰
ST_HEAVY = 1       # 疯狂喝水中 —— 深绿
ST_DRINK = 2       # 喝水中     —— 浅绿
ST_LUNCH = 3       # 午休中     —— 中性暗灰（固定段，不可选）
ST_WORK = 4        # 工作中     —— 黄
ST_DEEP = 5        # 埋头工作中 —— 红

ST_NAME = {ST_REST: "休息中", ST_HEAVY: "疯狂喝水中", ST_DRINK: "喝水中",
           ST_LUNCH: "午休中", ST_WORK: "工作中", ST_DEEP: "埋头工作中"}
ST_HEX = {ST_REST: "#6E7789", ST_HEAVY: "#1F9E63", ST_DRINK: "#74D6A3",
          ST_LUNCH: "#4E5866", ST_WORK: "#FFC24B", ST_DEEP: "#E5534B"}
ST_RGB = {k: tuple(int(v[i:i + 2], 16) for i in (1, 3, 5)) for k, v in ST_HEX.items()}

# 进度条的三层底：没走到 / 已走过无记录 / 午休还没走到
TRACK_RGB = (40, 45, 55)          # 底槽：进度还没到的地方保持这个「原来的暗色」
FILL_RGB = (58, 66, 80)           # 暗层：进度已经走过的整段先铺这层，再压状态色
LUNCH_DIM_RGB = (50, 56, 67)      # 午休未走到：只比底槽亮一点，留个位置感

# 实际薪资 vs 标定薪资：高于绿、低于红、持平沿用灰
WAGE_UP = "#5FD39B"
WAGE_DOWN = "#EF6E66"
WAGE_SAME = "#7B8497"
CHIP_BG = (30, 35, 44)


def wage_color(value, base):
    """实际值对比标定值：高 → 绿，低 → 红，持平（±0.1%）沿用底栏灰。"""
    if value is None or not base:
        return WAGE_SAME
    if value > base * 1.001:
        return WAGE_UP
    if value < base * 0.999:
        return WAGE_DOWN
    return WAGE_SAME


def _fade(c1, c2, p):
    """按进度 p 在两个颜色之间插值，用于模拟淡出（画布不支持逐项透明度）。"""
    p = max(0.0, min(1.0, p))
    return "#%02x%02x%02x" % tuple(int(c1[i] + (c2[i] - c1[i]) * p) for i in range(3))


# ---------------------------------------------------------------- 系统辅助
def enable_dpi_awareness():
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
        return
    except Exception:
        pass
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass


def system_dpi():
    try:
        hdc = ctypes.windll.user32.GetDC(0)
        dpi = ctypes.windll.gdi32.GetDeviceCaps(hdc, 88)
        ctypes.windll.user32.ReleaseDC(0, hdc)
        return dpi if dpi else 96
    except Exception:
        return 96


class POINT(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]


class RECT(ctypes.Structure):
    _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long),
                ("right", ctypes.c_long), ("bottom", ctypes.c_long)]


class MONITORINFO(ctypes.Structure):
    _fields_ = [("cbSize", ctypes.c_ulong), ("rcMonitor", RECT),
                ("rcWork", RECT), ("dwFlags", ctypes.c_ulong)]


def cursor_pos():
    pt = POINT()
    fn = ctypes.windll.user32.GetCursorPos
    fn.argtypes = [ctypes.POINTER(POINT)]
    fn.restype = ctypes.c_int
    fn(ctypes.byref(pt))
    return pt.x, pt.y


# GetAsyncKeyState 返回 SHORT，必须显式声明，否则高位是未定义的寄存器残留值
_get_async_key_state = ctypes.windll.user32.GetAsyncKeyState
_get_async_key_state.restype = ctypes.c_short
_get_async_key_state.argtypes = [ctypes.c_int]


def mouse_any_button_down():
    """返回 (当前是否按下, 自上次调用以来是否发生过按下)。"""
    try:
        left = _get_async_key_state(0x01)
        right = _get_async_key_state(0x02)
    except Exception:
        return False, False
    now_down = bool(left & 0x8000) or bool(right & 0x8000)
    since = bool(left & 0x0001) or bool(right & 0x0001)
    return now_down, since


def work_area_at(x, y):
    try:
        fn = ctypes.windll.user32.MonitorFromPoint
        fn.argtypes = [POINT, ctypes.c_ulong]
        fn.restype = ctypes.c_void_p
        hmon = fn(POINT(int(x), int(y)), 2)  # MONITOR_DEFAULTTONEAREST
        if not hmon:
            raise ctypes.WinError()
        mi = MONITORINFO()
        mi.cbSize = ctypes.sizeof(MONITORINFO)
        gi = ctypes.windll.user32.GetMonitorInfoW
        gi.argtypes = [ctypes.c_void_p, ctypes.POINTER(MONITORINFO)]
        gi.restype = ctypes.c_int
        if gi(hmon, ctypes.byref(mi)):
            r = mi.rcWork
            return r.left, r.top, r.right, r.bottom
    except Exception:
        pass
    u = ctypes.windll.user32
    return 0, 0, u.GetSystemMetrics(0), u.GetSystemMetrics(1)


class APPBARDATA(ctypes.Structure):
    _fields_ = [("cbSize", ctypes.c_ulong),
                ("hWnd", ctypes.c_void_p),
                ("uCallbackMessage", ctypes.c_uint),
                ("uEdge", ctypes.c_uint),
                ("rc", RECT),
                ("lParam", ctypes.c_void_p)]


def taskbar_info():
    """返回 (是否自动隐藏, 任务栏矩形, 贴边方向)。方向：0左 1上 2右 3下。"""
    try:
        fn = ctypes.windll.shell32.SHAppBarMessage
        fn.restype = ctypes.c_ulonglong
        abd = APPBARDATA()
        abd.cbSize = ctypes.sizeof(APPBARDATA)
        state = fn(0x00000004, ctypes.byref(abd))       # ABM_GETSTATE
        autohide = bool(state & 0x1)                     # ABS_AUTOHIDE
        abd2 = APPBARDATA()
        abd2.cbSize = ctypes.sizeof(APPBARDATA)
        if not fn(0x00000005, ctypes.byref(abd2)):       # ABM_GETTASKBARPOS
            return autohide, None, None
        r = abd2.rc
        return autohide, (r.left, r.top, r.right, r.bottom), abd2.uEdge
    except Exception:
        return False, None, None


def round_window_corners(win):
    try:
        hwnd = ctypes.windll.user32.GetParent(win.winfo_id()) or win.winfo_id()
        pref = ctypes.c_int(2)  # DWMWCP_ROUND
        ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 33, ctypes.byref(pref),
                                                   ctypes.sizeof(pref))
    except Exception:
        pass


# ---------------------------------------------------------------- 在岗信号
class LASTINPUTINFO(ctypes.Structure):
    _fields_ = [("cbSize", ctypes.c_uint), ("dwTime", ctypes.c_ulong)]


_k32 = ctypes.windll.kernel32
_u32 = ctypes.windll.user32
_k32.GetTickCount.restype = ctypes.c_ulong


def idle_seconds():
    """全系统空闲秒数（键鼠任一有动作都会清零），用单调 tick 计算，不受改系统时间影响。"""
    li = LASTINPUTINFO()
    li.cbSize = ctypes.sizeof(LASTINPUTINFO)
    try:
        if not _u32.GetLastInputInfo(ctypes.byref(li)):
            return 0.0
        diff = (_k32.GetTickCount() - li.dwTime) & 0xFFFFFFFF
        return diff / 1000.0
    except Exception:
        return 0.0


# ---------------------------------------------------------------- 配置
CONFIG_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), APP_NAME)
CONFIG_PATH = os.path.join(CONFIG_DIR, "config.json")
PID_PATH = os.path.join(CONFIG_DIR, "app.pid")
CRASH_PATH = os.path.join(CONFIG_DIR, "crash.log")

_crash_fh = None
try:
    os.makedirs(CONFIG_DIR, exist_ok=True)
    _crash_fh = open(CRASH_PATH, "a", buffering=1, encoding="utf-8")
    _crash_fh.write("\n=== {}  start pid={}  frozen={} ===\n".format(
        datetime.now(), os.getpid(), FROZEN))
    import faulthandler
    faulthandler.enable(_crash_fh, all_threads=True)
except Exception:
    _crash_fh = None


def crash_log(msg):
    if _crash_fh is None:
        return
    try:
        _crash_fh.write("{}  {}\n".format(datetime.now().strftime("%H:%M:%S"), msg))
    except Exception:
        pass

DEFAULTS = {
    # 首次运行（比如把 exe 发给别人）只给 1 块钱，避免泄露真实月薪；
    # 用户自己改过之后会写进 config.json，之后每次启动都读自己的值。
    "monthly": 1.0,
    "start_hour": 9,
    "end_hour": 18,
    "lunch_hour": 11.5,      # 午休开始（小时，11.5 = 11:30）
    "lunch_hours": 1.5,      # 午休时长（小时，支持 1.5 / 2.5）
}


class Config(dict):
    def __init__(self):
        super().__init__(DEFAULTS)
        try:
            if os.path.exists(CONFIG_PATH):
                with open(CONFIG_PATH, "r", encoding="utf-8") as fh:
                    data = json.load(fh)
                for k in DEFAULTS:
                    if k in data:
                        self[k] = data[k]
        except Exception:
            pass

    def save(self):
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            with open(CONFIG_PATH, "w", encoding="utf-8") as fh:
                json.dump(dict(self), fh, ensure_ascii=False, indent=2)
        except Exception:
            pass


# ---------------------------------------------------------------- 在岗统计
SAMPLE_CAP = 3.0           # 单次采样最多计入的秒数，防止休眠唤醒后一次性补记
PRESENCE_PATH = os.path.join(CONFIG_DIR, "presence.json")

# 唯一判据：过去 4 分钟内「有键鼠动作的秒数」占比
ACT_WINDOW = 240.0                # 统计窗口：4 分钟（第 20 轮缩到 2 分钟，第 21 轮放宽到 4 分钟）
ACT_BOUNDS = (0.23, 0.50, 0.77)   # 三档边界：疯狂喝水 | 喝水 | 工作 | 埋头工作
ACT_EPS = 0.02                    # 边界滞回，防止在分界线上来回跳档
LEVEL_STATE = (ST_HEAVY, ST_DRINK, ST_WORK, ST_DEEP)

# 四种状态各自的工时折算系数：喝水的那段按打折计入「实际工作时长」
# 疯狂喝水 1 小时只算 0.1 小时，喝水算 0.5；埋头工作按 2 倍算
STATE_WEIGHT = {ST_HEAVY: 0.1, ST_DRINK: 0.5, ST_WORK: 1.0, ST_DEEP: 2.0}
WORK_STATES = (ST_WORK, ST_DEEP)   # 真正在干活的两种，只有它们累加 work_raw
ACTIVE_STATES = (ST_HEAVY, ST_DRINK, ST_WORK, ST_DEEP)   # 需要记进时间轴的状态


class PresenceTracker:
    """在岗时长统计：班时内 + 键鼠活跃度达标，才算在岗。按天持久化。"""

    def __init__(self):
        self.day = date.today().isoformat()
        self.work_seconds = 0.0           # 实际工作时长：四态折算后累加（0.1/0.5/1.0/2.0）
        self.work_raw = 0.0               # 只累加「工作中 + 埋头工作中」，喝水时间靠钟面减它
        self.observed = 0.0               # 程序真正观测到的在班秒数（不分状态），实际薪资的分子靠它
        self.anchor_ts = time.time()      # 当天首次启动时刻，喝水只从这一刻开始算
        self._last_mono = time.monotonic()
        self._last_save = time.time()
        # 4 分钟滑窗：每秒一个采样，(monotonic, 该周期内是否动过键鼠)
        self.samples = deque()
        self.level = 2                   # 0 疯狂喝水 / 1 喝水 / 2 工作 / 3 埋头工作
        self.timeline = {}               # 分钟序号(0~1439) → 该分钟占优的状态码
        self._cur_min = None
        self._cur_counts = {}
        self._load()

    # --- 持久化
    def _load(self):
        try:
            with open(PRESENCE_PATH, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            if data.get("day") == date.today().isoformat():
                self.day = data["day"]
                self.work_seconds = float(data.get("work_seconds", 0.0))
                # 第 19 轮起 work_raw 只记「真在干活」的秒数；老存档缺这个字段就退回工作秒数
                self.work_raw = float(data.get("work_raw", self.work_seconds))
                # 第 22 轮新增：未观测在班秒数。老存档缺它就退回 work_raw（只会低估，不会虚高）
                self.observed = float(data.get("observed", self.work_raw))
                self.anchor_ts = float(data.get("anchor_ts", time.time()))
                for k, v in (data.get("timeline") or {}).items():
                    try:
                        self.timeline[int(k)] = int(v)
                    except Exception:
                        pass
                return
        except Exception:
            pass
        self.anchor_ts = time.time()
        self.work_seconds = 0.0
        self.work_raw = 0.0
        self.observed = 0.0
        self.save(force=True)

    def save(self, force=False):
        if not force and time.time() - self._last_save < 10.0:
            return
        self._last_save = time.time()
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            with open(PRESENCE_PATH, "w", encoding="utf-8") as fh:
                json.dump({"day": self.day,
                           "work_seconds": round(self.work_seconds, 1),
                           "work_raw": round(self.work_raw, 1),
                           "observed": round(self.observed, 1),
                           "anchor_ts": self.anchor_ts,
                           "timeline": {str(k): v for k, v in self.timeline.items()}},
                          fh)
        except Exception:
            pass

    # --- 采样
    def _roll_day(self):
        today = date.today().isoformat()
        if today != self.day:
            self.day = today
            self.work_seconds = 0.0
            self.work_raw = 0.0
            self.observed = 0.0
            self.timeline = {}
            self._cur_min = None
            self._cur_counts = {}
            self.anchor_ts = time.time()
            self.samples.clear()
            self.level = 2
            self.save(force=True)

    def _trim(self, mono):
        while self.samples and mono - self.samples[0][0] > ACT_WINDOW:
            self.samples.popleft()

    def activity_ratio(self):
        """过去 4 分钟内「有键鼠动作的秒数」占比，0~1。"""
        if not self.samples:
            return 0.0
        return sum(1 for _t, a in self.samples if a) / len(self.samples)

    def _update_level(self):
        """四档切换：跨过边界立即换档，边界上下留 2% 滞回，避免来回跳。"""
        if not self.samples:             # 窗口为空（刚跨天或首格被丢弃），本轮不判，保持原状
            return
        ratio = self.activity_ratio()
        lvl = 0
        for b in ACT_BOUNDS:
            if ratio >= b:
                lvl += 1
        if lvl > self.level and ratio < ACT_BOUNDS[self.level] + ACT_EPS:
            lvl = self.level
        elif lvl < self.level and ratio > ACT_BOUNDS[lvl] - ACT_EPS:
            lvl = self.level
        self.level = lvl

    # --- 时间轴（进度条数据源）
    def _record(self, code, now, dt):
        """每秒的状态丢进当前分钟桶；换分钟时把占优状态写进时间轴。"""
        mi = now.hour * 60 + now.minute
        if mi != self._cur_min:
            self._flush_minute()
            self._cur_min = mi
            self._cur_counts = {}
        if code in ACTIVE_STATES:
            self._cur_counts[code] = self._cur_counts.get(code, 0.0) + dt

    def _flush_minute(self):
        if self._cur_min is None or not self._cur_counts:
            return
        best = max(self._cur_counts.items(), key=lambda kv: kv[1])[0]
        self.timeline[self._cur_min] = best

    def current_minute(self, live_code=None):
        """当前这一分钟的 (分钟序号, 占优状态)，让进度条右端能实时变色。"""
        if self._cur_min is None:
            return None
        if live_code in ACTIVE_STATES:
            return self._cur_min, live_code
        if self._cur_counts:
            return self._cur_min, max(self._cur_counts.items(), key=lambda kv: kv[1])[0]
        return None

    def sample(self, engine):
        mono = time.monotonic()
        dt = mono - self._last_mono
        if dt < 0.95:
            return
        self._last_mono = mono
        self._roll_day()

        # 这一采样周期内动过键鼠吗（静止秒数小于间隔，即此期间有过输入）
        moved = idle_seconds() < min(dt, 2.0)
        if dt <= 3.0:                      # 唤醒或卡顿后的长间隔不计入窗口，防止占比被拉偏
            self.samples.append((mono, 1 if moved else 0))
        self._trim(mono)
        self._update_level()

        now = datetime.now()
        code, _ = engine.live_state(now)
        dtc = min(dt, SAMPLE_CAP)
        if engine.is_workday(now) and engine.in_window(now):
            self.observed += dtc                       # 不分状态，记「程序看过这段班时」
            weight = STATE_WEIGHT.get(code)
            if weight is not None:
                self.work_seconds += dtc * weight      # 四态都按系数折算进实际工作时长
            if code in WORK_STATES:
                self.work_raw += dtc                   # 只有真在干活才算「没喝水」
        self._record(code, now, dtc)
        self.save()


# ---------------------------------------------------------------- 计薪引擎
def days_in_month(d):
    nxt = datetime(d.year + (1 if d.month == 12 else 0), 1 if d.month == 12 else d.month + 1, 1)
    return (nxt - datetime(d.year, d.month, 1)).days


class Engine:
    def __init__(self, cfg, tracker=None):
        self.cfg = cfg
        self.tracker = tracker

    @property
    def lunch_window(self):
        """午休区间（秒），自动夹到班时之内。"""
        start = float(self.cfg["start_hour"]) * 3600.0
        end = float(self.cfg["end_hour"]) * 3600.0
        ls = float(self.cfg.get("lunch_hour", 11.5)) * 3600.0
        le = ls + max(0.0, float(self.cfg.get("lunch_hours", 0.0))) * 3600.0
        ls = min(max(ls, start), end)
        le = min(max(le, ls), end)
        return ls, le

    @property
    def day_len(self):
        """每日标定工作时长：班时减去午休。"""
        start = float(self.cfg["start_hour"]) * 3600.0
        end = float(self.cfg["end_hour"]) * 3600.0
        ls, le = self.lunch_window
        return max(3600.0, (end - start) - (le - ls))

    @property
    def work_days(self):
        """本月工作日数量：按当前日历自动统计（周一至周五，不设人工选项）。"""
        now = datetime.now()
        return sum(1 for d in range(1, days_in_month(now) + 1)
                   if self.is_workday(datetime(now.year, now.month, d)))

    @property
    def monthly_work_seconds(self):
        return max(1, self.work_days) * self.day_len

    @property
    def per_second(self):
        """秒薪：日薪 ÷ 标定班时，固定不变（钱按班时照发，摸鱼也照发）。"""
        return float(self.cfg["monthly"]) / self.monthly_work_seconds

    @property
    def per_hour(self):
        return float(self.cfg["monthly"]) / (max(1, self.work_days) * (self.day_len / 3600.0))

    @property
    def per_day(self):
        return float(self.cfg["monthly"]) / max(1, self.work_days)

    @staticmethod
    def is_workday(d):
        return d.weekday() < 5

    def clock_seconds(self, now):
        return now.hour * 3600 + now.minute * 60 + now.second + now.microsecond / 1e6

    def in_window(self, now):
        """是否处在“计薪时段”（班时内且不在午休）。"""
        start = float(self.cfg["start_hour"]) * 3600.0
        end = float(self.cfg["end_hour"]) * 3600.0
        t = self.clock_seconds(now)
        if not (start <= t < end):
            return False
        ls, le = self.lunch_window
        return not (ls <= t < le)

    def paid_seconds_today(self, now):
        """今天截至当前、扣掉午休后的计薪秒数。"""
        start = float(self.cfg["start_hour"]) * 3600.0
        end = float(self.cfg["end_hour"]) * 3600.0
        t = self.clock_seconds(now)
        if t <= start:
            return 0.0
        x = min(t, end)
        total = x - start
        ls, le = self.lunch_window
        total -= max(0.0, min(x, le) - max(start, ls))
        return max(0.0, total)

    def seconds_today(self, now):
        if not self.is_workday(now):
            return 0.0
        return self.paid_seconds_today(now)

    def seconds_month(self, now):
        total = 0.0
        for day in range(1, now.day + 1):
            if not self.is_workday(datetime(now.year, now.month, day)):
                continue
            total += self.day_len if day < now.day else self.paid_seconds_today(now)
        return total

    def bar_axis(self):
        """进度条的横轴：上班到下班的整段钟面（含午休），返回 (起, 止) 秒。"""
        start = float(self.cfg["start_hour"]) * 3600.0
        end = float(self.cfg["end_hour"]) * 3600.0
        if end <= start:
            end = start + 3600.0
        return start, end

    def clock_progress(self, now):
        """进度条百分比：此刻在 上班→下班 整段里走了多少，与条形严格对齐。"""
        if not self.is_workday(now):
            return 0.0
        start, end = self.bar_axis()
        return max(0.0, min(1.0, (self.clock_seconds(now) - start) / (end - start)))

    def month_earned(self, now):
        return self.per_second * self.seconds_month(now)

    def today_earned(self, now):
        return self.per_second * self.seconds_today(now)

    def is_working_now(self, now):
        return self.is_workday(now) and self.in_window(now)

    # ---- 在岗相关
    @property
    def presence(self):
        return self.tracker.work_seconds if self.tracker else 0.0

    def observed_earned(self):
        """程序观测期间赚到的钱：分子与分母同源，都只覆盖「程序开着的那段班时」。

        不能直接用 today_earned()——它从当天班时起算，与程序何时启动无关。程序晚开
        或中途重启时，分子含了没观测到的班时、分母不含，实际时薪会被放大十几倍。
        """
        if self.tracker is None:
            return 0.0
        return self.per_second * self.tracker.observed

    def live_second_wage(self, now):
        """实际秒薪 = 观测期间已赚 ÷ 实际工作时长。

        实际工作时长 = 四种状态按时长折算后累加（疯狂喝水 0.1 / 喝水 0.5 /
        工作中 1.0 / 埋头工作中 2.0）。为 0 时除数为零，返回 None，界面显示 ∞。
        """
        p = self.presence
        if p <= 0:
            return None
        return self.observed_earned() / p

    def real_hour_wage(self, now):
        """实际时薪：就是秒速 × 3600，两个数字永远同源。"""
        w = self.live_second_wage(now)
        return None if w is None else w * 3600.0

    def slack_seconds(self, now):
        """喝水 = 启动以来已过的计薪时段 − 真正在干活的秒数（work_raw）。

        第 19 轮起喝水不打折也不加成：摸鱼多久就是多久，折算系数只作用于「实际工作时长」。
        面板没打开的那段时间没有采样，仍按钟面口径计入喝水。
        """
        if not self.is_workday(now):
            return None
        tr = self.tracker
        if tr is None:
            return 0.0
        elapsed = self.paid_seconds_today(now)
        anchor = datetime.fromtimestamp(tr.anchor_ts)
        if anchor.date() == now.date():
            elapsed = max(0.0, elapsed - self.paid_seconds_today(anchor))
        else:
            elapsed = 0.0
        return max(0.0, elapsed - tr.work_raw)

    def live_state(self, now):
        """当前状态码 + 判定原因。午休 / 班外 / 非工作日一律归到对应的静止状态。"""
        if not self.is_workday(now):
            return ST_REST, "今天不是工作日，暂停计时"
        t = self.clock_seconds(now)
        start, end = self.bar_axis()
        ls, le = self.lunch_window
        if ls <= t < le:
            return ST_LUNCH, "处于午休时段，暂停计时"
        if t < start:
            return ST_REST, "还没到上班时间，暂停计时"
        if t >= end:
            return ST_REST, "已过下班时间，暂停计时"
        tr = self.tracker
        if tr is None:
            return ST_WORK, "键鼠活跃度判定，正常计时"
        body = "键鼠活跃度 {}%".format(int(round(tr.activity_ratio() * 100)))
        return LEVEL_STATE[tr.level], body

    def duty_state(self, now):
        """当前状态：(显示文字, 圆点颜色, 判定原因)，颜色与进度条同一套。"""
        code, reason = self.live_state(now)
        return ST_NAME[code], ST_HEX[code], reason

    # ---- 进度条时间轴
    def _minute_code(self, minute, live_code):
        """某一分钟的状态码：当前这一分钟优先用实时状态，其余读落盘的时间轴。"""
        tr = self.tracker
        if tr is None:
            return None
        cur = tr.current_minute(live_code)
        if cur and cur[0] == minute:
            return cur[1]
        return tr.timeline.get(minute)

    def timeline_runs(self, now):
        """把当日记录压成同状态连续段：[(起比例, 止比例, 状态码)]，右端不超过此刻。"""
        tr = self.tracker
        if tr is None:
            return []
        start, end = self.bar_axis()
        span = max(1.0, end - start)
        now_s = self.clock_seconds(now)
        live, _ = self.live_state(now)

        s_min = int(start // 60)
        e_min = int(end // 60) + 1
        keys = set(tr.timeline)
        cur = tr.current_minute(live)
        if cur:
            keys.add(cur[0])
        keys = sorted(k for k in keys if s_min <= k <= e_min)

        runs = []
        run = None
        for k in keys:
            c = self._minute_code(k, live)
            if c is None:
                continue
            if run and run[2] == c and k == run[1] + 1:
                run[1] = k
            else:
                if run:
                    runs.append(run)
                run = [k, k, c]
        if run:
            runs.append(run)

        segs = []
        for k0, k1, c in runs:
            t0 = max(start, k0 * 60.0)
            t1 = min(end, (k1 + 1) * 60.0, now_s)
            if t1 - t0 < 1.0:
                continue
            segs.append(((t0 - start) / span, (t1 - start) / span, c))
        return segs

    def state_breakdown(self, now):
        """当日已过班时里各状态各占多久：返回 (总秒数, {状态码: 秒数})。

        分母是「上班→此刻」的整段钟面（含午休）。没记录的分钟记到 ST_REST，
        界面上显示为「未计时」——面板启动前和被关掉的那段时间都在这里。
        """
        tr = self.tracker
        start, end = self.bar_axis()
        cut = min(self.clock_seconds(now), end)
        total = cut - start
        if total <= 0:
            return 0.0, {}
        live, _ = self.live_state(now)
        ls, le = self.lunch_window
        acc = {}
        for m in range(int(start // 60), int(cut // 60) + 1):
            t0 = max(start, m * 60.0)
            t1 = min(cut, (m + 1) * 60.0)
            if t1 <= t0:
                continue
            ov = max(0.0, min(t1, le) - max(t0, ls))
            if ov > 0:
                acc[ST_LUNCH] = acc.get(ST_LUNCH, 0.0) + ov
            rest = (t1 - t0) - ov
            if rest > 0:
                code = (self._minute_code(m, live) if tr else None) or ST_REST
                acc[code] = acc.get(code, 0.0) + rest
        return total, acc

    def bar_hover_text(self, ratio):
        """进度条悬停文案：「HH:MM–HH:MM ｜ 状态」。未来区域不提示。"""
        now = datetime.now()
        start, end = self.bar_axis()
        t = start + max(0.0, min(1.0, ratio)) * (end - start)
        now_s = self.clock_seconds(now)
        if t > now_s + 1.0:
            return None
        ls, le = self.lunch_window
        if ls <= t < le:
            return "{}–{} ｜ {}".format(fmt_hm(ls), fmt_hm(le), ST_NAME[ST_LUNCH])

        minute = int(t // 60.0)
        live, _ = self.live_state(now)
        code = self._minute_code(minute, live)
        if code is None:                      # 没记录 = 休息中，不上色但如实说明
            t0 = max(start, minute * 60.0)
            t1 = min(end, t0 + 60.0, now_s)
            return "{}–{} ｜ {}".format(fmt_hm(t0), fmt_hm(t1), ST_NAME[ST_REST])

        k0 = k1 = minute
        while self._minute_code(k0 - 1, live) == code:
            k0 -= 1
        while self._minute_code(k1 + 1, live) == code:
            k1 += 1
        t0 = max(start, k0 * 60.0)
        t1 = min(end, (k1 + 1) * 60.0, now_s)
        return "{}–{} ｜ {}".format(fmt_hm(t0), fmt_hm(t1), ST_NAME[code])


def money_parts(value):
    v = round(float(value), 2)
    ip = int(v)
    dp = int(round((v - ip) * 100))
    if dp >= 100:
        ip += 1
        dp -= 100
    return "{:,}".format(ip), ".{:02d}".format(dp)


def fmt_duration(seconds):
    """喝水时长：1s / 5m12s / 1h2m3s / —。"""
    if seconds is None:
        return "—"
    s = int(max(0, seconds))
    h, rem = divmod(s, 3600)
    m, sec = divmod(rem, 60)
    if h:
        return "{}h{}m{}s".format(h, m, sec)
    if m:
        return "{}m{}s".format(m, sec)
    return "{}s".format(sec)


def fmt_wage(w):
    w = float(w)
    if abs(w - round(w)) < 1e-9:
        return "{:,.0f}".format(w)
    return "{:,.2f}".format(w).rstrip("0").rstrip(".")


def fmt_hour(v):
    """小时数转输入框文本：9 → 9，1.5 → 1.5。"""
    v = float(v)
    if abs(v - round(v)) < 1e-9:
        return "{:d}".format(int(round(v)))
    return ("%.2f" % v).rstrip("0").rstrip(".")


def fmt_clock(v):
    """小时数转时钟文本：9 → 09:00，11.5 → 11:30。"""
    v = float(v) % 24.0
    h = int(v)
    m = int(round((v - h) * 60))
    if m >= 60:
        h, m = (h + 1) % 24, 0
    return "{:02d}:{:02d}".format(h, m)


def fmt_hm(seconds):
    """当日秒数转时钟文本：30600 → 08:30。"""
    s = int(max(0, min(seconds, 86399)))
    return "{:02d}:{:02d}".format(s // 3600, (s % 3600) // 60)


def parse_hour(text, clock_style=False):
    """支持 9 / 9.5 / 09:30 / 9.30 几种写法，统一成小时数。"""
    s = str(text).strip().replace("：", ":").replace("。", ".")
    if ":" in s:
        hh, mm = s.split(":", 1)
        return float(hh) + float(mm) / 60.0
    if clock_style and "." in s:
        hh, mm = s.split(".", 1)
        if len(mm) == 2 and mm.isdigit() and int(mm) < 60:
            return float(hh) + int(mm) / 60.0
    return float(s)


# ---------------------------------------------------------------- 图形资源
_pill_cache = {}
_bg_cache = {}


def pill_image(w, h, r, fill, outline=None, ow=1):
    key = (w, h, r, fill, outline, ow)
    if key in _pill_cache:
        return _pill_cache[key]
    ss = 4
    img = Image.new("RGBA", (w * ss, h * ss), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rounded_rectangle([0, 0, w * ss - 1, h * ss - 1], radius=max(0, r) * ss, fill=fill,
                        outline=outline, width=ow * ss if outline else 0)
    img = img.resize((w, h), Image.LANCZOS)
    ph = ImageTk.PhotoImage(img)
    _pill_cache[key] = ph
    return ph


def bar_image(w, h, segs):
    """进度条整条一次画完：灰底 + 各状态色段，最后套圆角遮罩。

    segs = ((起像素, 止像素, (r,g,b)), ...)，后画的覆盖先画的（午休固定段压在最上层）。
    条宽仅 288px、每秒重画一次，成本可以忽略，因此不做缓存（缓存反而要处理旧图释放）。
    """
    ss = 2
    n = w * ss
    m = h * ss
    img = Image.new("RGB", (n, m), TRACK_RGB)
    d = ImageDraw.Draw(img)
    for x0, x1, rgb in segs:
        a = int(round(x0 * ss))
        b = int(round(x1 * ss))
        if b <= a:
            continue
        d.rectangle([a, 0, b - 1, m - 1], fill=rgb)
    mask = Image.new("L", (n, m), 0)
    ImageDraw.Draw(mask).rounded_rectangle([0, 0, n - 1, m - 1], radius=m // 2, fill=255)
    out = Image.new("RGB", (n, m), CARD_BOT)
    out.paste(img, (0, 0), mask)
    return ImageTk.PhotoImage(out.resize((w, h), Image.LANCZOS))


def card_image(w, h):
    key = (w, h)
    if key in _bg_cache:
        return _bg_cache[key]
    ss = 2
    img = Image.new("RGB", (w * ss, h * ss), CARD_BOT)
    d = ImageDraw.Draw(img)
    for y in range(h * ss):
        t = y / max(1, h * ss - 1)
        c = tuple(int(CARD_TOP[i] + (CARD_BOT[i] - CARD_TOP[i]) * t) for i in range(3))
        d.line([(0, y), (w * ss, y)], fill=c)
    d.rectangle([0, 0, w * ss - 1, h * ss - 1], outline=BORDER, width=max(1, ss))
    img = img.resize((w, h), Image.LANCZOS)
    ph = ImageTk.PhotoImage(img)
    _bg_cache[key] = ph
    return ph


def tray_icon_image(size=64):
    ss = 4
    n = size * ss
    img = Image.new("RGBA", (n, n), (0, 0, 0, 0))
    grad = Image.new("RGB", (n, n), (255, 194, 75))
    gd = ImageDraw.Draw(grad)
    for y in range(n):
        t = y / (n - 1)
        c = (int(255 + (232 - 255) * t), int(198 + (160 - 198) * t), int(96 + (44 - 96) * t))
        gd.line([(0, y), (n, y)], fill=c)
    mask = Image.new("L", (n, n), 0)
    ImageDraw.Draw(mask).ellipse([0, 0, n - 1, n - 1], fill=255)
    img.paste(grad, (0, 0), mask)

    d = ImageDraw.Draw(img)
    d.ellipse([int(n * 0.11), int(n * 0.11), int(n * 0.89), int(n * 0.89)],
              outline=(84, 58, 10, 200), width=max(2, int(n * 0.03)))
    font = None
    for path in (r"C:\Windows\Fonts\seguisb.ttf", r"C:\Windows\Fonts\arialbd.ttf"):
        try:
            font = ImageFont.truetype(path, int(n * 0.58))
            break
        except Exception:
            continue
    if font is None:
        font = ImageFont.load_default()
    bbox = d.textbbox((0, 0), "¥", font=font)
    tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
    d.text(((n - tw) / 2 - bbox[0], (n - th) / 2 - bbox[1]), "¥", font=font, fill=(44, 30, 5, 255))
    return img.resize((size, size), Image.LANCZOS)


def write_icon_file():
    try:
        os.makedirs(ICON_DIR, exist_ok=True)
        tray_icon_image(256).save(ICON_PATH, sizes=[(16, 16), (24, 24), (32, 32),
                                                    (48, 48), (64, 64), (256, 256)])
    except Exception:
        pass


# ---------------------------------------------------------------- 胶囊按钮
class Pill:
    def __init__(self, canvas, x, y, w, h, text, command=None, kind="ghost", font=None):
        self.c = canvas
        self.w, self.h = w, h
        self.radius = h // 2
        self.command = command
        self.kind = kind
        self._hover = False
        self._img = self._image()
        self.img_id = canvas.create_image(x, y, anchor="nw", image=self._img)
        self.text_id = canvas.create_text(x + w // 2, y + h // 2 - 1, text=text,
                                          fill=self._text_color(), font=font, anchor="center")
        for item in (self.img_id, self.text_id):
            canvas.tag_bind(item, "<Enter>", self._on_enter)
            canvas.tag_bind(item, "<Leave>", self._on_leave)
            canvas.tag_bind(item, "<ButtonRelease-1>", self._on_click)

    def _image(self):
        if self.kind == "primary":
            fill = (255, 205, 104) if self._hover else (255, 199, 88)
            return pill_image(self.w, self.h, self.radius, fill, None, 0)
        fill = GHOST_HOVER if self._hover else GHOST_BG
        return pill_image(self.w, self.h, self.radius, fill, (58, 65, 78), 1)

    def _text_color(self):
        if self.kind == "primary":
            return "#2A1D04"
        return TEXT if self._hover else "#C6CEDC"

    def refresh(self):
        self._img = self._image()
        self.c.itemconfigure(self.img_id, image=self._img)
        self.c.itemconfigure(self.text_id, fill=self._text_color())

    def _on_enter(self, _e):
        if not self.command and self.kind != "primary":
            return
        self._hover = True
        self.refresh()
        self.c.configure(cursor="hand2")

    def _on_leave(self, _e):
        self._hover = False
        self.refresh()
        self.c.configure(cursor="")

    def _on_click(self, _e):
        if self.command:
            self.command()


# ---------------------------------------------------------------- 弹窗
class Popup:
    W = 332
    H_MAIN = 278
    H_SET = 312

    def __init__(self, app):
        self.app = app
        self.cfg = app.cfg
        self.engine = app.engine
        self.S = app.S
        self.root = app.root
        self.fam_cn = app.fam_cn
        self.fam_num = app.fam_num

        self.visible = False
        self.settings_visible = False
        self.shown_at = 0.0
        self.last_hidden = 0.0
        self.settings_built = False
        self._rect = None
        self._ticks = []
        self._last_render = 0.0
        self._shown_value = None

        self.win = tk.Toplevel(self.root)
        self.win.withdraw()
        self.win.overrideredirect(True)
        self.win.attributes("-topmost", True)
        self.win.configure(bg=CARD_BG_HEX)

        self.Wp, self.Hp = self.px(self.W), self.px(self.H_MAIN)

        self.c_main = tk.Canvas(self.win, bd=0, highlightthickness=0, bg=CARD_BG_HEX,
                                width=self.Wp, height=self.Hp)
        self.c_set = tk.Canvas(self.win, bd=0, highlightthickness=0, bg=CARD_BG_HEX,
                               width=self.Wp, height=self.px(self.H_SET))
        self.c_main.pack(fill="both", expand=True)

        self._build_main()

        # 悬停提示（独立小窗，四角透明）：胶囊用判定依据，进度条用「时间段 ｜ 状态」
        self._state_reason = ""
        self._tip_visible = False
        self._tip_text = ""
        self._tip_mode = ""
        self._tip_anchor = None
        self._tip_size = (0, 0)
        self._tip_w, self._tip_h = self.px(150), self.px(28)
        self._tip = tk.Toplevel(self.root)
        self._tip.withdraw()
        self._tip.overrideredirect(True)
        self._tip.attributes("-topmost", True)
        self._tip.configure(bg=CARD_BG_HEX)
        try:
            self._tip.attributes("-transparentcolor", CARD_BG_HEX)
        except Exception:
            pass
        self._tip_c = tk.Canvas(self._tip, bd=0, highlightthickness=0, bg=CARD_BG_HEX)
        self._tip_c.pack(fill="both", expand=True)
        self.c_main.bind("<Motion>", self._on_motion)
        self.c_main.bind("<Leave>", lambda e: self._tip_hide())

        self.win.bind("<Escape>", lambda e: self.hide())

    # ---------------------------------------------------------- 基础
    def px(self, v):
        return int(round(v * self.S))

    def f(self, family, size, style="normal"):
        return (family, -self.px(size), style)

    # ---------------------------------------------------------- 主视图
    def _build_main(self):
        c = self.c_main
        W, H, PAD = self.Wp, self.Hp, self.px(22)
        c.delete("all")
        c.create_image(0, 0, anchor="nw", image=card_image(W, H))

        f_label = self.f(self.fam_num, 12.5)
        f_big = self.f(self.fam_num, 38, "bold")
        f_dec = self.f(self.fam_num, 21, "bold")
        f_cur = self.f(self.fam_num, 17, "bold")
        f_stat = self.f(self.fam_num, 17, "bold")
        f_small = self.f(self.fam_cn, 11.5)

        self.f_int = tkfont.Font(family=self.fam_num, size=-self.px(38), weight="bold")
        self.f_dec_font = tkfont.Font(family=self.fam_num, size=-self.px(21), weight="bold")

        c.create_text(PAD, self.px(18), text="本月已赚", anchor="nw", fill=MUTED, font=f_label)

        # 状态胶囊（右上）：六种状态共用进度条那套颜色，宽度按最长标签自适应
        # 字体必须挂在 self 上：tkinter.Font 被回收会把 Tk 里的字体一起删掉
        self.f_chip = tkfont.Font(family=self.fam_cn, size=-self.px(10.5))
        widest = max(self.f_chip.measure(n) for n in ST_NAME.values())
        self._chip_h = self.px(21)
        self._dot_dx = self.px(12)
        self._text_dx = self.px(22)
        self._chip_w = self._text_dx + widest + self.px(11)
        self._chip_x = W - PAD - self._chip_w
        self._chip_y = self.px(13)
        self._chip_cy = self._chip_y + self._chip_h // 2
        c.create_image(self._chip_x, self._chip_y, anchor="nw",
                       image=pill_image(self._chip_w, self._chip_h, self._chip_h // 2,
                                        CHIP_BG, None, 0))
        r = self.px(3)
        dot_x = self._chip_x + self._dot_dx
        self.i_chip_dot = c.create_oval(dot_x - r, self._chip_cy - r, dot_x + r, self._chip_cy + r,
                                        fill=ST_HEX[ST_WORK], outline=ST_HEX[ST_WORK])
        self.i_chip_text = c.create_text(self._chip_x + self._text_dx, self._chip_cy,
                                         text="工作中", anchor="w",
                                         fill="#B9C2D2", font=self.f_chip)

        base = self.px(82)
        c.create_text(PAD, base, text="¥", anchor="sw", fill=GOLD, font=f_cur)
        self.i_int = c.create_text(PAD + self.px(17), base, text="0", anchor="sw",
                                   fill=TEXT, font=f_big)
        self.i_dec = c.create_text(PAD + self.px(60), base, text=".00", anchor="sw",
                                   fill="#7F8AA0", font=f_dec)

        c.create_line(PAD, self.px(97), W - PAD, self.px(97), fill="#272D38")

        # 三列：末列放宽，容得下「7h59m59s」；秒薪下方挂一行「实际」小字
        xs = [PAD, PAD + self.px(98), PAD + self.px(178)]
        for x, text in zip(xs, ("今日已赚", "秒薪", "喝水时间")):
            c.create_text(x, self.px(108), text=text, anchor="nw", fill=MUTED, font=f_label)

        self.i_today = c.create_text(xs[0], self.px(126), text="¥0.00", anchor="nw",
                                     fill=TEXT, font=f_stat)
        self.i_rate = c.create_text(xs[1], self.px(126), text="¥0.00", anchor="nw",
                                    fill="#D8DEE9", font=f_stat)
        self.i_real = c.create_text(xs[1], self.px(148), text="实际 ¥0.00", anchor="nw",
                                    fill="#7B8497", font=self.f(self.fam_cn, 10))
        self.i_slack = c.create_text(xs[2], self.px(126), text="0s", anchor="nw",
                                     fill="#D8DEE9", font=f_stat)

        c.create_text(PAD, self.px(166), text="本日进度", anchor="nw", fill=MUTED, font=f_small)
        self.i_prog = c.create_text(W - PAD, self.px(166), text="0.0%", anchor="ne",
                                    fill=GOLD, font=f_small)

        # 进度条：一条 上班→下班 的钟面尺，灰底先铺，状态色段每秒重画一次
        bar_y, bar_h = self.px(186), self.px(7)
        c.create_image(PAD, bar_y, anchor="nw",
                       image=pill_image(W - 2 * PAD, bar_h, bar_h // 2, TRACK_RGB, None, 0))
        self.bar_img_id = None
        self._bar_photo = None

        # 底栏拆三段：「（实际 ¥X）」单独一段，才能按高于/低于标定值上色
        # 字号 10 而非 10.5：早高峰「实际」会到四位数（¥1,047.62），10.5 会顶出卡片右边缘
        # 字体挂在 self 上，避免 tkinter.Font 被回收后 Tk 字体一并删除
        self.f_foot = tkfont.Font(family=self.fam_cn, size=-self.px(10))
        self._foot_y = self.px(206)
        self.i_foot_a = c.create_text(PAD, self._foot_y, text="", anchor="nw",
                                      fill="#7B8497", font=self.f_foot)
        self.i_foot_b = c.create_text(PAD, self._foot_y, text="", anchor="nw",
                                      fill=WAGE_SAME, font=self.f_foot)
        self.i_foot_c = c.create_text(PAD, self._foot_y, text="", anchor="nw",
                                      fill="#7B8497", font=self.f_foot)

        bw, bh, by = self.px(86), self.px(31), self.px(227)
        self.btn_settings = Pill(c, PAD, by, bw, bh, "设置", self.open_settings,
                                 font=self.f(self.fam_cn, 12))
        self.btn_quit = Pill(c, W - PAD - bw, by, bw, bh, "退出", self.app.quit,
                             font=self.f(self.fam_cn, 12))

    # ---------------------------------------------------------- 设置视图
    def _build_settings(self):
        W, H, PAD = self.Wp, self.px(self.H_SET), self.px(22)
        c = self.c_set
        c.delete("all")
        c.create_image(0, 0, anchor="nw", image=card_image(W, H))

        f_title = self.f(self.fam_cn, 16, "bold")
        f_label = self.f(self.fam_cn, 12)
        box_w = W - 2 * PAD
        col_w = self.px(140)
        gap = self.px(8)
        right_x = PAD + col_w + gap

        c.create_text(PAD, self.px(16), text="设置", anchor="nw", fill=TEXT, font=f_title)

        def field(x, y, w, label, text, attr, size=14):
            c.create_text(x, self.px(y), text=label, anchor="nw", fill=MUTED, font=f_label)
            c.create_image(x, self.px(y + 18), anchor="nw",
                           image=pill_image(w, self.px(36), self.px(9),
                                            INPUT_BG, (60, 67, 82), 1))
            e = self._entry(x + self.px(13), self.px(y + 27), w - self.px(26), size)
            e.insert(0, text)
            setattr(self, attr, e)

        # 月薪（整行）
        c.create_text(PAD, self.px(48), text="月薪（元）", anchor="nw", fill=MUTED, font=f_label)
        c.create_image(PAD, self.px(66), anchor="nw",
                       image=pill_image(box_w, self.px(36), self.px(9), INPUT_BG, (60, 67, 82), 1))
        self.e_wage = self._entry(PAD + self.px(13), self.px(75), box_w - self.px(26), 15)
        self.e_wage.insert(0, fmt_wage(self.cfg["monthly"]))

        # 上下班
        field(PAD, 118, col_w, "上班（时间）", fmt_clock(self.cfg["start_hour"]), "e_start")
        field(right_x, 118, col_w, "下班（时间）", fmt_clock(self.cfg["end_hour"]), "e_end")

        # 午休
        field(PAD, 188, col_w, "午休开始（时间）",
              fmt_clock(self.cfg.get("lunch_hour", 11.5)), "e_lunch")
        field(right_x, 188, col_w, "午休时长（小时）",
              fmt_hour(self.cfg.get("lunch_hours", 1.5)), "e_lunch_len")

        bw, bh, by = self.px(140), self.px(34), self.px(260)
        self.btn_save = Pill(c, PAD, by, bw, bh, "保存", self.save_settings, kind="primary",
                             font=self.f(self.fam_cn, 12.5, "bold"))
        self.btn_cancel = Pill(c, W - PAD - bw, by, bw, bh, "取消", self.cancel_settings,
                               font=self.f(self.fam_cn, 12.5))

        self.settings_built = True

    def _entry(self, x, y, w, size):
        e = tk.Entry(self.c_set, bd=0, relief="flat", bg="#242933", fg=TEXT,
                     insertbackground=GOLD, highlightthickness=0,
                     font=(self.fam_num, -self.px(size)), justify="left")
        self.c_set.create_window(x, y, anchor="nw", window=e, width=w)
        e.bind("<Return>", lambda ev: self.save_settings())
        e.bind("<FocusIn>", lambda ev: e.configure(bg="#2C323E"))
        e.bind("<FocusOut>", lambda ev: e.configure(bg="#242933"))
        return e

    # ---------------------------------------------------------- 视图切换
    def _switch_to(self, settings):
        self.settings_visible = settings
        h = self.px(self.H_SET if settings else self.H_MAIN)
        canvas = self.c_set if settings else self.c_main
        (self.c_main if settings else self.c_set).pack_forget()
        canvas.pack(fill="both", expand=True)
        self.win.geometry("{}x{}".format(self.Wp, h))
        canvas.update_idletasks()

    def open_settings(self):
        if not self.settings_built:
            self._build_settings()
        self._tip_hide()
        self._switch_to(True)
        self._place()
        self.e_wage.focus_set()
        try:
            self.e_wage.icursor("end")
        except Exception:
            pass

    def cancel_settings(self):
        self._revert_form()
        self._switch_to(False)
        self._place()

    def _revert_form(self):
        if not self.settings_built:
            return
        for e, text in ((self.e_wage, fmt_wage(self.cfg["monthly"])),
                        (self.e_start, fmt_clock(self.cfg["start_hour"])),
                        (self.e_end, fmt_clock(self.cfg["end_hour"])),
                        (self.e_lunch, fmt_clock(self.cfg.get("lunch_hour", 11.5))),
                        (self.e_lunch_len, fmt_hour(self.cfg.get("lunch_hours", 1.5)))):
            e.delete(0, "end")
            e.insert(0, text)

    def save_settings(self):
        try:
            wage = float(str(self.e_wage.get()).replace(",", "").strip())
            sh = parse_hour(self.e_start.get(), True)
            eh = parse_hour(self.e_end.get(), True)
            lh = parse_hour(self.e_lunch.get(), True)
            ll = parse_hour(self.e_lunch_len.get(), True)
            if wage <= 0 or eh - sh < 1.0 or ll < 0:
                raise ValueError
        except Exception:
            self._flash_error()
            return

        sh = min(max(sh, 0.0), 23.0)
        eh = min(max(eh, sh + 1.0), 24.0)
        lh = min(max(lh, sh), eh)
        ll = min(ll, eh - sh - 0.5)

        self.cfg["monthly"] = wage
        self.cfg["start_hour"] = round(sh, 4)
        self.cfg["end_hour"] = round(eh, 4)
        self.cfg["lunch_hour"] = round(lh, 4)
        self.cfg["lunch_hours"] = round(max(0.0, ll), 4)
        self.cfg.save()
        self._revert_form()
        self._switch_to(False)
        self._place()
        self._refresh()

    def _flash_error(self):
        entries = (self.e_wage, self.e_start, self.e_end, self.e_lunch, self.e_lunch_len)
        for e in entries:
            e.configure(bg="#3A2530")
        self.win.after(900, lambda: [e.configure(bg="#242933") for e in entries])

    # ---------------------------------------------------------- 位置 / 显隐
    def _place(self):
        h = self.px(self.H_SET if self.settings_visible else self.H_MAIN)
        cx, cy = cursor_pos()
        left, top, right, bottom = work_area_at(cx, cy)
        x = right - self.Wp - self.px(12)
        y = bottom - h - self.px(12)

        # 任务栏自动隐藏时，工作区不会让出任务栏高度，需要额外避让
        autohide, rect, edge = taskbar_info()
        if autohide and rect and edge == 3:
            if x + self.Wp > rect[0] and x < rect[2]:
                y -= (rect[3] - rect[1])
        self.win.geometry("{}x{}+{}+{}".format(self.Wp, h, x, y))
        self._rect = (x, y, self.Wp, h)

    def show(self):
        if self.visible:
            self._switch_to(False)
            self._place()
            self.win.lift()
            self.win.focus_force()
            return
        self._switch_to(False)
        self._place()
        self.win.attributes("-alpha", 0.0)
        self.win.deiconify()
        self.win.lift()
        self.win.attributes("-topmost", True)
        self.win.focus_force()
        round_window_corners(self.win)
        self.visible = True
        self.shown_at = time.time()
        self._last_render = 0.0    # 让第一帧立刻绘制
        self._shown_value = None
        mouse_any_button_down()   # 清掉打开面板那一下点击留下的“已按下”标记
        self._fade_in(0.0)

    def _fade_in(self, a):
        if not self.visible:
            return
        a = min(1.0, a + 0.24)
        try:
            self.win.attributes("-alpha", a)
        except Exception:
            return
        if a < 1.0:
            self.win.after(14, lambda: self._fade_in(a))

    def hide(self):
        if not self.visible:
            return
        self.visible = False
        self._tip_hide()
        for item, _born, _x in self._ticks:
            try:
                self.c_main.delete(item)
            except Exception:
                pass
        self._ticks = []
        self.win.withdraw()
        try:
            self.win.attributes("-alpha", 1.0)
        except Exception:
            pass
        self.last_hidden = time.time()

    def watch_outside_click(self):
        """轮询鼠标按键：在面板外按下任何键即收起，行为可预期、不依赖焦点。"""
        if not self.visible or not self._rect:
            return
        now_down, since = mouse_any_button_down()
        if not now_down and not (since and time.time() - self.shown_at > 0.25):
            return
        x, y = cursor_pos()
        rx, ry, rw, rh = self._rect
        if not (rx <= x <= rx + rw and ry <= y <= ry + rh):
            self.hide()

    def toggle(self):
        if self.visible:
            self.hide()
            return
        if time.time() - self.last_hidden < 0.25:
            return
        self.show()

    # ---------------------------------------------------------- 数值刷新
    def _refresh(self):
        if not self.visible or self.settings_visible:
            return
        now = datetime.now()
        ts = time.time()

        # 数字一秒一动：整秒才重绘一次，跳字与数字严格同步
        if self._last_render == 0 or ts - self._last_render >= 1.0:
            self._last_render = ts
            self._render_numbers(now)

        self._animate_ticks(now)

    def _render_numbers(self, now):
        c = self.c_main
        PAD = self.px(22)

        value = self.engine.month_earned(now)
        ip, dp = money_parts(value)
        c.itemconfigure(self.i_int, text=ip)
        iw = self.f_int.measure(ip)
        dec_x = PAD + self.px(17) + iw - self.px(2)
        c.coords(self.i_dec, dec_x, self.px(82))
        c.itemconfigure(self.i_dec, text=dp)

        c.itemconfigure(self.i_today, text="¥{:,.2f}".format(self.engine.today_earned(now)))
        c.itemconfigure(self.i_rate, text="¥{:.2f}".format(self.engine.per_second))

        # 实际秒薪：工作时长为 0 时除数为零，显示 ∞；这一行不上色
        speed = self.engine.live_second_wage(now)
        c.itemconfigure(self.i_real,
                        text="实际 ∞" if speed is None else "实际 ¥{:.2f}".format(speed))

        slack = self.engine.slack_seconds(now)
        c.itemconfigure(self.i_slack, text=fmt_duration(slack))

        self._render_state(now)

        prog = self.engine.clock_progress(now)
        c.itemconfigure(self.i_prog, text="{:.1f}%".format(prog * 100))
        self._draw_bar(now)

        # 底栏三段拼一行；只有「（实际 ¥X）」按高于/低于标定值换色
        rh = self.engine.real_hour_wage(now)
        real = "∞" if rh is None else "¥{:,.2f}".format(rh)
        foot_a = "日薪 ¥{:,.2f} · 时薪 ¥{:,.2f}".format(self.engine.per_day, self.engine.per_hour)
        foot_b = "（实际 {}）".format(real)
        foot_c = " · {} 个工作日".format(self.engine.work_days)
        xb = PAD + self.f_foot.measure(foot_a)
        xc = xb + self.f_foot.measure(foot_b)
        c.itemconfigure(self.i_foot_a, text=foot_a)
        c.itemconfigure(self.i_foot_b, text=foot_b,
                        fill=wage_color(rh, self.engine.per_hour))
        c.itemconfigure(self.i_foot_c, text=foot_c)
        c.coords(self.i_foot_b, xb, self._foot_y)
        c.coords(self.i_foot_c, xc, self._foot_y)

        working = self.engine.is_working_now(now)

        # 与上一秒的显示值求差，跳字金额永远等于数字实际跳动量
        prev = self._shown_value
        self._shown_value = value
        if working and prev is not None:
            delta = round(value, 2) - round(prev, 2)
            if delta >= 0.005:
                self._spawn_tick(delta, self.Wp - PAD)

    # ---------------------------------------------------------- 状态胶囊
    def _render_state(self, now):
        label, color, reason = self.engine.duty_state(now)
        self._state_reason = reason
        c = self.c_main
        c.itemconfigure(self.i_chip_text, text=label)
        c.itemconfigure(self.i_chip_dot, fill=color, outline=color)
        if self._tip_visible and self._tip_mode == "chip":
            self._tip_show(reason)

    def _bar_rect(self):
        PAD = self.px(22)
        bar_y, bar_h = self.px(186), self.px(7)
        pad = self.px(5)
        return PAD, bar_y - pad, self.Wp - PAD, bar_y + bar_h + pad

    def _on_motion(self, e):
        # 「本日进度」那一行 → 当日状态占比
        x0, y0, x1, y1 = self._prog_rect()
        if x0 <= e.x <= x1 and y0 <= e.y <= y1:
            title, rows = self._progress_rows(datetime.now())
            if rows:
                self._tip_show_panel(title, rows,
                                     anchor=(self.win.winfo_rootx() + e.x,
                                             self.win.winfo_rooty() + e.y))
            else:
                self._tip_hide()
            return

        # 进度条 → 「时间段 ｜ 状态」
        x0, y0, x1, y1 = self._bar_rect()
        if x0 <= e.x <= x1 and y0 <= e.y <= y1:
            full_w = max(1, x1 - x0)
            text = self.engine.bar_hover_text((e.x - x0) / float(full_w))
            if text:
                self._tip_show(text, anchor=(self.win.winfo_rootx() + e.x,
                                             self.win.winfo_rooty() + e.y))
            else:
                self._tip_hide()
            return

        pad = self.px(3)
        inside = (self._chip_x - pad <= e.x <= self._chip_x + self._chip_w + pad and
                  self._chip_y - pad <= e.y <= self._chip_y + self._chip_h + pad)
        if inside:
            self._tip_show(self._state_reason)
        elif self._tip_visible:
            self._tip_hide()

    def _prog_rect(self):
        """「本日进度」文字行的命中区（到条形上沿为止，不抢条形的气泡）。"""
        PAD = self.px(22)
        return PAD, self.px(160), self.Wp - PAD, self.px(180)

    def _progress_rows(self, now):
        """四种活动状态的内部占比（分母 = 四态之和），今天没出现过的状态不列。

        午休与未计时只是时间轴上的留白，不参与这张表——它们不是「你当时在干什么」。
        """
        if not self.engine.is_workday(now):      # 非工作日不弹，全是空白没有意义
            return "", []
        _, acc = self.engine.state_breakdown(now)
        active = sum(acc.get(c, 0.0) for c in ACTIVE_STATES)
        if active <= 0:
            return "", []
        rows = []
        for code in (ST_WORK, ST_DEEP, ST_DRINK, ST_HEAVY):   # 从最活跃到最不活跃
            sec = acc.get(code, 0.0)
            if sec / active < 0.005:             # 没出现（或只闪了一下）就不占一行
                continue
            rows.append((ST_HEX[code], ST_NAME[code], "{:.0f}%".format(sec / active * 100)))
        return "活动 {}".format(fmt_duration(active)), rows

    def _tip_show(self, text, anchor=None):
        """单行气泡。anchor 为空 = 贴胶囊（判定依据）；给定 (屏幕x, 屏幕y) = 跟着鼠标走。"""
        text = text or ""
        if not text or not self.visible:
            return
        mode = "chip" if anchor is None else "bar"
        if mode == "chip":                  # 贴胶囊：右对齐卡片内边，y 由卡片位置决定
            anchor = (self.win.winfo_rootx() + self.Wp - self.px(22), 0)

        c = self._tip_c
        if text != self._tip_text:
            self._tip_text = text
            fnt = tkfont.Font(family=self.fam_cn, size=-self.px(10.5))
            w = min(self.px(320), fnt.measure(text) + self.px(24))
            h = self.px(28)
            c.configure(width=w, height=h)
            c.delete("all")
            c.create_image(0, 0, anchor="nw",
                           image=pill_image(w, h, self.px(7), (30, 34, 42), (58, 65, 78), 1))
            c.create_text(w // 2, h // 2, text=text, anchor="center",
                          fill="#C4CDDB", font=(self.fam_cn, -self.px(10.5)))
            self._tip_w, self._tip_h = w, h
        else:
            w, h = self._tip_w, self._tip_h
        self._tip_place(w, h, mode, anchor)

    def _tip_show_panel(self, title, rows, anchor):
        """多行气泡：色点 + 名称 + 数值，用于「本日进度」那一行的状态占比。"""
        if not rows or not self.visible:
            return
        key = "panel|" + title + "|" + "|".join(l + v for _, l, v in rows)
        if key != self._tip_text:
            self._tip_text = key
            c = self._tip_c
            fnt = tkfont.Font(family=self.fam_cn, size=-self.px(10.5))
            r = self.px(2.5)
            pad = self.px(11)
            line_h = self.px(18)
            gap = self.px(9)
            dot_w = int(r * 2)
            lab_w = max(fnt.measure(l) for _, l, _ in rows)
            val_w = max(fnt.measure(v) for _, _, v in rows)
            w = pad * 2 + dot_w + gap + lab_w + self.px(16) + val_w
            h = pad * 2 + line_h * (len(rows) + 1)
            c.configure(width=w, height=h)
            c.delete("all")
            c.create_image(0, 0, anchor="nw",
                           image=pill_image(w, h, self.px(8), (30, 34, 42), (58, 65, 78), 1))
            c.create_text(pad, pad, text=title, anchor="nw", fill="#7B8497",
                          font=(self.fam_cn, -self.px(9.5)))
            y = pad + line_h
            for color, label, value in rows:
                cy = y + line_h // 2
                c.create_oval(pad, cy - r, pad + dot_w, cy + r, fill=color, outline=color)
                c.create_text(pad + dot_w + gap, cy, text=label, anchor="w", fill="#C4CDDB",
                              font=(self.fam_cn, -self.px(10.5)))
                c.create_text(w - pad, cy, text=value, anchor="e", fill="#95A0B2",
                              font=(self.fam_cn, -self.px(10.5)))
                y += line_h
            self._tip_w, self._tip_h = w, h
        else:
            w, h = self._tip_w, self._tip_h
        self._tip_place(w, h, "panel", anchor)

    def _tip_place(self, w, h, mode, anchor):
        """定位：贴胶囊放卡片上方；跟光标放右下 16/20px，贴边翻到另一侧。"""
        # 尺寸没变、光标挪动不到 2px 就不重设窗口，
        # 避免高频 Motion 反复调 MonitorFromPoint
        if (self._tip_visible and self._tip_mode == mode and self._tip_size == (w, h)
                and self._tip_anchor is not None
                and abs(anchor[0] - self._tip_anchor[0]) < 2
                and abs(anchor[1] - self._tip_anchor[1]) < 2):
            return
        self._tip_mode = mode
        self._tip_anchor = anchor
        self._tip_size = (w, h)

        pad = self.px(4)
        sx, sy = anchor
        left, top, right, bottom = work_area_at(sx, self.win.winfo_rooty())

        if mode == "chip":
            x = sx - w
            cy = self.win.winfo_rooty() - h - self.px(7)
            if cy < top + pad:      # 上方放不下就落回卡片内
                cy = self.win.winfo_rooty() + self._chip_y + self._chip_h + self.px(6)
        else:
            # 鼠标右下方 16/20px，贴边就翻到另一侧，始终挨着光标
            x = sx + self.px(16)
            cy = sy + self.px(20)
            if x + w > right - pad:
                x = sx - w - self.px(16)
            if cy + h > bottom - pad:
                cy = sy - h - self.px(20)
        x = max(left + pad, min(x, right - w - pad))
        cy = max(top + pad, min(cy, bottom - h - pad))
        self._tip.geometry("{}x{}+{}+{}".format(int(w), int(h), int(x), int(cy)))
        if not self._tip_visible:
            self._tip.deiconify()
            self._tip.lift()
            self._tip_visible = True

    def _tip_hide(self):
        if not self._tip_visible:
            return
        self._tip_visible = False
        self._tip_text = ""
        self._tip_mode = ""
        self._tip_anchor = None
        self._tip_size = (0, 0)
        try:
            self._tip.withdraw()
        except Exception:
            pass

    # ---------------------------------------------------------- 每秒跳字
    def _animate_ticks(self, now):
        """跳字在金额正上方：上浮 10px 并渐隐，每次持续 1 秒。"""
        c = self.c_main
        ts = now.timestamp()
        alive = []
        for item, born, x in self._ticks:
            age = ts - born
            if age >= 1.0:
                c.delete(item)
                continue
            c.coords(item, x, self.px(72) - self.px(9) * age)
            c.itemconfigure(item, fill=_fade(GOLD_RGB, TICK_BG, age))
            alive.append((item, born, x))
        self._ticks = alive

    def _spawn_tick(self, delta, x):
        item = self.c_main.create_text(
            x, self.px(72), text="+¥{:.2f}".format(delta),
            anchor="se", fill=GOLD, font=self.f(self.fam_num, 17, "bold"))
        self._ticks.append((item, datetime.now().timestamp(), x))
        if len(self._ticks) > 4:
            old, _, _ = self._ticks.pop(0)
            self.c_main.delete(old)

    def _draw_bar(self, now):
        """整条重画：先铺「已走过」的暗层，再压状态色段，午休段按已过/未到分两级亮度。

        明暗分界就是此刻：走过的才有底色，没走到的一律保持原轨道色，
        午休块在没走到时只留一个极暗的位置标记，走过后才亮成正常的暗黄。
        """
        c = self.c_main
        PAD = self.px(22)
        full_w = self.Wp - 2 * PAD
        bar_y, bar_h = self.px(186), self.px(7)
        prog_w = self.engine.clock_progress(now) * full_w

        segs = []
        if prog_w > 0:                      # 已走过的整段先铺一层暗层
            segs.append((0.0, prog_w, FILL_RGB))
        for r0, r1, code in self.engine.timeline_runs(now):
            segs.append((r0 * full_w, min(r1 * full_w, prog_w), ST_RGB[code]))

        start, end = self.engine.bar_axis()
        ls, le = self.engine.lunch_window
        if le - ls >= 60:
            x0 = (ls - start) / (end - start) * full_w
            x1 = (le - start) / (end - start) * full_w
            if x0 < prog_w:                 # 已走到：正常暗黄
                segs.append((x0, min(x1, prog_w), ST_RGB[ST_LUNCH]))
            if x1 > prog_w:                 # 还没走到：只留位置，亮度压到贴底
                segs.append((max(x0, prog_w), x1, LUNCH_DIM_RGB))

        img = bar_image(full_w, bar_h, tuple(segs))
        if self.bar_img_id is None:
            self.bar_img_id = c.create_image(PAD, bar_y, anchor="nw", image=img)
        else:
            c.itemconfigure(self.bar_img_id, image=img)
        self._bar_photo = img


# ---------------------------------------------------------------- 托盘应用
class App:
    def __init__(self):
        enable_dpi_awareness()
        self.S = system_dpi() / 96.0
        self.cfg = Config()
        self.tracker = PresenceTracker()
        self.engine = Engine(self.cfg, self.tracker)

        self.root = tk.Tk()
        self.root.withdraw()
        self.root.title(APP_NAME)
        self.fam_cn = self._pick(["Microsoft YaHei UI", "Microsoft YaHei", "Segoe UI"])
        self.fam_num = self._pick(["Segoe UI Semibold", "Segoe UI", "Microsoft YaHei UI"])

        self.popup = Popup(self)
        self.commands = queue.Queue()
        self._last_tip = 0.0

        self.icon = pystray.Icon(
            APP_NAME,
            tray_icon_image(64),
            "本月已赚",
            pystray.Menu(
                pystray.MenuItem("查看本月收入", lambda: self.post("toggle", "tray"), default=True),
                pystray.MenuItem("设置…", lambda: self.post("settings", "tray-menu")),
                pystray.Menu.SEPARATOR,
                pystray.MenuItem("退出", lambda: self.post("quit", "tray-menu")),
            ),
        )

        write_icon_file()
        self._create_wake_event()
        self._loop()

    def _pick(self, names):
        try:
            fams = set(tkfont.families(self.root))
        except Exception:
            fams = set()
        for n in names:
            if n in fams:
                return n
        return "Segoe UI"

    def post(self, cmd, src="app"):
        if os.environ.get("ET_DEBUG"):
            try:
                with open(os.path.join(HERE, "debug.log"), "a", encoding="utf-8") as fh:
                    fh.write("{} [{}] post {}\n".format(
                        datetime.now().strftime("%H:%M:%S.%f")[:-3], src, cmd))
            except Exception:
                pass
        self.commands.put(cmd)

    # --- 主循环（100ms）
    def _loop(self):
        try:
            while True:
                cmd = self.commands.get_nowait()
                if cmd == "toggle":
                    self.popup.toggle()
                elif cmd == "show":
                    self.popup.show()
                elif cmd == "settings":
                    if not self.popup.visible:
                        self.popup.show()
                    self.popup.open_settings()
                elif cmd == "quit":
                    self.quit()
                    return
        except queue.Empty:
            pass

        try:
            self.tracker.sample(self.engine)
            self.popup._refresh()
            self.popup.watch_outside_click()
            self._update_tooltip()
        except Exception:
            pass

        self.root.after(100, self._loop)

    def _update_tooltip(self):
        if time.time() - self._last_tip < 1.0:
            return
        self._last_tip = time.time()
        try:
            now = datetime.now()
            v = self.engine.month_earned(now)
            slack = self.engine.slack_seconds(now)
            tip = "本月已赚 ¥{:,.2f}".format(v)
            if slack is not None:
                tip += " · 喝水 {}".format(fmt_duration(slack))
            self.icon.title = tip
        except Exception:
            pass

    # --- 单实例唤醒
    def _create_wake_event(self):
        try:
            self._event = ctypes.windll.kernel32.CreateEventW(None, False, False, EVENT_NAME)
        except Exception:
            self._event = None
        if not self._event:
            return
        threading.Thread(target=self._wait_wake, daemon=True).start()

    def _wait_wake(self):
        while True:
            r = ctypes.windll.kernel32.WaitForSingleObject(self._event, 400)
            if r == 0:
                self.post("toggle", "wake")

    # --- 生命周期
    def run(self):
        threading.Thread(target=self.icon.run, daemon=True).start()

        self.root.mainloop()

    def quit(self):
        try:
            import traceback
            crash_log("quit() called from:\n" + "".join(traceback.format_stack()[-6:]))
        except Exception:
            pass
        try:
            self.tracker.save(force=True)
        except Exception:
            pass
        try:
            self.icon.stop()
        except Exception:
            pass
        try:
            os.remove(PID_PATH)
        except Exception:
            pass
        try:
            self.root.quit()
            self.root.destroy()
        except Exception:
            pass
        os._exit(0)


def _pid_alive(pid):
    """判断某个 PID 是否仍是活动进程（避免残留事件句柄把新实例挡在门外）。"""
    if not pid:
        return False
    try:
        k = ctypes.windll.kernel32
        k.OpenProcess.restype = ctypes.c_void_p
        k.OpenProcess.argtypes = [ctypes.c_ulong, ctypes.c_int, ctypes.c_ulong]
        h = k.OpenProcess(0x1000, False, int(pid))   # PROCESS_QUERY_LIMITED_INFORMATION
        if not h:
            return False
        try:
            if k.WaitForSingleObject(ctypes.c_void_p(h), 0) == 0:
                return False          # 进程已退出
            # 再核对映像名，避免 PID 被无关进程复用时误判
            k.QueryFullProcessImageNameW.restype = ctypes.c_int
            k.QueryFullProcessImageNameW.argtypes = [ctypes.c_void_p, ctypes.c_ulong,
                                                     ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_ulong)]
            buf = ctypes.create_unicode_buffer(1024)
            size = ctypes.c_ulong(1024)
            if not k.QueryFullProcessImageNameW(ctypes.c_void_p(h), 0, buf, ctypes.byref(size)):
                return False
            return os.path.basename(buf.value).lower() == os.path.basename(sys.executable).lower()
        finally:
            k.CloseHandle(ctypes.c_void_p(h))
    except Exception:
        return False


def already_running():
    pid = 0
    try:
        with open(PID_PATH, "r", encoding="utf-8") as fh:
            pid = int(fh.read().strip() or 0)
    except Exception:
        pid = 0

    if _pid_alive(pid):
        try:
            h = ctypes.windll.kernel32.OpenEventW(0x0002, False, EVENT_NAME)
            if h:
                ctypes.windll.kernel32.SetEvent(h)
                ctypes.windll.kernel32.CloseHandle(h)
        except Exception:
            pass
        return True

    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(PID_PATH, "w", encoding="utf-8") as fh:
            fh.write(str(os.getpid()))
    except Exception:
        pass
    return False


def main():
    crash_log("main() enter")
    if already_running():
        crash_log("already running, exit")
        return
    app = App()
    crash_log("app created")
    if "--settings" in sys.argv:
        app.post("settings")
    elif "--silent" not in sys.argv:
        app.post("show")
    app.run()


if __name__ == "__main__":
    main()
