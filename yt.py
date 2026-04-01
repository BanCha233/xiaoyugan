# ==================== 猛兽派对钓鱼辅助（无音效无图片版） ====================
# 基于 IYIcode/hu-hu-fishing-demo 优化，遵循 MIT 协议
# 移除音效、GUI图片，保留核心钓鱼功能

import ctypes
import time
import sys
import random
import traceback
import os
import threading
import queue
import logging
from typing import Optional, Tuple

import cv2
import numpy as np
import pygetwindow as gw
import pyautogui
import mss
import keyboard
import win32gui
import win32con
import win32api
import tkinter as tk
import tkinter.font as tkfont

# -------------------- 日志配置 --------------------
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler()]
)
logger = logging.getLogger(__name__)

# -------------------- 资源路径适配 --------------------
def resource_path(relative_path: str) -> str:
    """获取资源文件绝对路径（支持 PyInstaller 打包）"""
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)

# -------------------- 全局配置 --------------------
class Config:
    # 游戏窗口标题
    WINDOW_TITLES = ["猛兽派对", "Party Animals", "party animals"]
    
    # 数字变化检测区域 (相对坐标，绝对宽高)
    NUMBER_REGION = (0.873, 0.897, 19, 16)
    NUMBER_SIMILARITY_THRESHOLD = 0.95
    
    # F 按钮区域 (用于鱼桶满检测)
    F_BUTTON_REGION = (0.4600, 0.9154, 0.0781, 0.0273)
    F_BUTTON_SIMILARITY_THRESHOLD = 0.85
    F_BUTTON_MIN_CONSECUTIVE = 2
    
    # 抛竿成功颜色检测区域
    CAST_SUCCESS_REGION = (0.5645, 0.9193, 0.0049, 0.0065)
    CAST_SUCCESS_TARGET_BGR = np.array([41.6, 186.9, 249.6], dtype=np.float32)
    CAST_COLOR_TOLERANCE = 50.0
    
    # 五角星品质检测区域
    STAR_REGION = (0.40, 0.05, 0.20, 0.15)
    STAR_TEMPLATE = "star_template.png"
    COLOR_REGION_OFFSET_X = -45
    COLOR_REGION_WIDTH = 120
    
    # 品质颜色映射 (RGB)
    QUALITY_COLORS = {
        "标准": (183, 186, 193),
        "非凡": (144, 198, 90),
        "稀有": (112, 174, 241),
        "史诗": (171, 102, 251),
        "传奇": (248, 197, 68)
    }
    
    # 超时设置
    BITE_TIMEOUT = 60
    CAST_FAILURE_CHECK_SEC = 7
    BUCKET_FULL_WAIT_SEC = 60
    BUCKET_FULL_MAX_RETRIES = 5

# 全局状态（线程安全）
star_quality_count = {q: 0 for q in Config.QUALITY_COLORS.keys()}
stats_lock = threading.Lock()

# 全局控制标志
fishing_paused = True
pause_lock = threading.Lock()

# 全局 GUI 窗口引用
log_window = None
log_window_lock = threading.Lock()

# -------------------- 窗口与截图管理 --------------------
class WindowManager:
    def __init__(self):
        self.hwnd = None
        self.left = self.top = self.width = self.height = 0
    
    def find_window(self) -> bool:
        for title in Config.WINDOW_TITLES:
            try:
                wins = gw.getWindowsWithTitle(title)
                if wins and hasattr(wins[0], '_hWnd'):
                    self.hwnd = wins[0]._hWnd
                    break
            except Exception as e:
                logger.error(f"查找窗口 '{title}' 出错: {e}")
        if not self.hwnd:
            return False
        
        # 激活窗口
        try:
            window = gw.getWindowsWithTitle(Config.WINDOW_TITLES[0])[0]
            window.activate()
            time.sleep(0.8)
        except Exception:
            pass
        
        # 获取客户区位置和大小
        try:
            win_left, win_top, win_right, win_bottom = win32gui.GetWindowRect(self.hwnd)
            client_width, client_height = win32gui.GetClientRect(self.hwnd)[2:]
            self.left = win_left + (win_right - win_left - client_width) // 2
            self.top = win_top + (win_bottom - win_top - client_height) - (win_right - win_left - client_width) // 2
            self.width = client_width
            self.height = client_height
            if self.width <= 0 or self.height <= 0:
                raise ValueError("窗口尺寸无效")
            logger.info(f"客户区: {self.width}x{self.height} @ ({self.left}, {self.top})")
            return True
        except Exception as e:
            logger.error(f"获取窗口客户区失败: {e}")
            return False
    
    def capture(self, sct: mss.mss) -> np.ndarray:
        """截图当前窗口内容，返回 BGR 格式 numpy 数组"""
        region = {"top": self.top, "left": self.left, "width": self.width, "height": self.height}
        img = sct.grab(region)
        return np.array(img)[:, :, :3]  # 去掉 alpha 通道

win_mgr = WindowManager()

# -------------------- ROI 提取与图像处理 --------------------
def extract_roi(frame: np.ndarray, rel_x: float, rel_y: float, rel_w: float, rel_h: float,
                window_w: int, window_h: int) -> Optional[np.ndarray]:
    x = int(rel_x * window_w)
    y = int(rel_y * window_h)
    w = int(rel_w * window_w)
    h = int(rel_h * window_h)
    
    if w <= 0 or h <= 0 or x + w > frame.shape[1] or y + h > frame.shape[0]:
        return None
    return frame[y:y+h, x:x+w]

def preprocess_binary(img: np.ndarray) -> np.ndarray:
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    _, binary = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
    return binary

# -------------------- 数字变化检测器（咬钩检测） --------------------
class NumberChangeTrigger:
    def __init__(self, rel_x: float, rel_y: float, w: int, h: int,
                 threshold: float = 0.95, interval: float = 0.3):
        self.rel_x = rel_x
        self.rel_y = rel_y
        self.w = w
        self.h = h
        self.threshold = threshold
        self.interval = interval
        self.base_binary = None
        self.last_trigger_time = 0
    
    def set_base(self, frame: np.ndarray, window_w: int, window_h: int) -> bool:
        roi = extract_roi(frame, self.rel_x, self.rel_y, self.w/window_w, self.h/window_h,
                          window_w, window_h)
        if roi is None or roi.size == 0:
            return False
        self.base_binary = preprocess_binary(roi)
        return True
    
    def should_reel(self, frame: np.ndarray, window_w: int, window_h: int) -> Tuple[bool, float]:
        now = time.time()
        if now - self.last_trigger_time < self.interval:
            return False, 1.0
        if self.base_binary is None:
            return False, 1.0
        
        roi = extract_roi(frame, self.rel_x, self.rel_y, self.w/window_w, self.h/window_h,
                          window_w, window_h)
        if roi is None or roi.size == 0:
            return False, 1.0
        
        current = preprocess_binary(roi)
        if current.shape != self.base_binary.shape:
            return False, 1.0
        
        diff = cv2.absdiff(self.base_binary, current)
        diff_ratio = np.sum(diff > 0) / diff.size
        similarity = 1.0 - diff_ratio
        
        if similarity < self.threshold:
            self.base_binary = current
            self.last_trigger_time = now
            return True, similarity
        return False, similarity

# -------------------- F按钮变化检测器（鱼桶满） --------------------
class FButtonChangeTrigger:
    def __init__(self, rel_x: float, rel_y: float, rel_w: float, rel_h: float,
                 threshold: float = 0.85, min_consecutive: int = 2, interval: float = 0.2):
        self.rel_x = rel_x
        self.rel_y = rel_y
        self.rel_w = rel_w
        self.rel_h = rel_h
        self.threshold = threshold
        self.min_consecutive = min_consecutive
        self.interval = interval
        self.base_binary = None
        self.consecutive_match = 0
        self.last_trigger_time = 0
    
    def set_base(self, frame: np.ndarray, window_w: int, window_h: int) -> bool:
        roi = extract_roi(frame, self.rel_x, self.rel_y, self.rel_w, self.rel_h, window_w, window_h)
        if roi is None or roi.size == 0:
            return False
        self.base_binary = preprocess_binary(roi)
        return True
    
    def check_bucket_full(self, frame: np.ndarray, window_w: int, window_h: int) -> Tuple[bool, float]:
        now = time.time()
        if now - self.last_trigger_time < self.interval:
            return False, 1.0
        if self.base_binary is None:
            return False, 1.0
        
        roi = extract_roi(frame, self.rel_x, self.rel_y, self.rel_w, self.rel_h, window_w, window_h)
        if roi is None or roi.size == 0:
            return False, 1.0
        
        current = preprocess_binary(roi)
        if current.shape != self.base_binary.shape:
            return False, 1.0
        
        diff = cv2.absdiff(self.base_binary, current)
        diff_ratio = np.sum(diff > 0) / diff.size
        similarity = 1.0 - diff_ratio
        
        if similarity > self.threshold:
            self.consecutive_match += 1
        else:
            self.consecutive_match = 0
        
        if self.consecutive_match >= self.min_consecutive:
            self.last_trigger_time = now
            return True, similarity
        return False, similarity

# -------------------- 颜色与鼠标操作 --------------------
def get_pixel_color_abs(x: int, y: int) -> Tuple[int, int, int]:
    try:
        return pyautogui.pixel(x, y)
    except Exception as e:
        raise RuntimeError(f"获取像素颜色失败 ({x},{y}): {e}")

def is_color_in_range(base_rgb: Tuple[int, int, int], current_rgb: Tuple[int, int, int], tolerance: int = 12) -> bool:
    return all(abs(base - cur) <= tolerance for base, cur in zip(base_rgb, current_rgb))

# 鼠标低级操作
PUL = ctypes.POINTER(ctypes.c_ulong)
class MOUSEINPUT(ctypes.Structure):
    _fields_ = [("dx", ctypes.c_long), ("dy", ctypes.c_long), ("mouseData", ctypes.c_ulong),
                ("dwFlags", ctypes.c_ulong), ("time", ctypes.c_ulong), ("dwExtraInfo", PUL)]

class INPUT_I(ctypes.Union):
    _fields_ = [("mi", MOUSEINPUT)]

class INPUT(ctypes.Structure):
    _fields_ = [("type", ctypes.c_ulong), ("ii", INPUT_I)]

SendInput = ctypes.windll.user32.SendInput

def _send_mouse_event(flags, dx=0, dy=0, data=0):
    extra = ctypes.c_ulong(0)
    mi = MOUSEINPUT(dx, dy, data, flags, 0, ctypes.pointer(extra))
    command = INPUT(type=0, ii=INPUT_I(mi=mi))
    SendInput(1, ctypes.byref(command), ctypes.sizeof(command))

def left_down(): _send_mouse_event(0x0002)
def left_up(): _send_mouse_event(0x0004)
def left_click():
    left_down()
    time.sleep(0.05)
    left_up()

# -------------------- 品质检测 --------------------
def detect_star_quality(frame: np.ndarray) -> Optional[str]:
    """检测五角星品质，返回品质名称，并更新全局统计"""
    global star_quality_count
    try:
        h_img, w_img = frame.shape[:2]
        template_path = resource_path(Config.STAR_TEMPLATE)
        if not os.path.exists(template_path):
            logger.error(f"五角星模板缺失: {template_path}")
            return None
        template = cv2.imread(template_path)
        if template is None:
            logger.error("五角星模板加载失败")
            return None
        template_gray = cv2.cvtColor(template, cv2.COLOR_BGR2GRAY)
        th, tw = template_gray.shape[:2]
        
        rx, ry, rw, rh = Config.STAR_REGION
        sx, sy, sw, sh = int(w_img*rx), int(h_img*ry), int(w_img*rw), int(h_img*rh)
        detect_region = frame[sy:sy+sh, sx:sx+sw]
        detect_gray = cv2.cvtColor(detect_region, cv2.COLOR_BGR2GRAY)
        
        SCALES = [1.0, 0.9, 0.8, 0.7, 0.6]
        best_score = 0
        best_loc = None
        best_tw, best_th = tw, th
        for s in SCALES:
            t_resized = cv2.resize(template_gray, (int(tw*s), int(th*s)), interpolation=cv2.INTER_AREA)
            res = cv2.matchTemplate(detect_gray, t_resized, cv2.TM_CCOEFF_NORMED)
            _, max_val, _, max_loc = cv2.minMaxLoc(res)
            if max_val > best_score:
                best_score = max_val
                best_loc = max_loc
                best_tw, best_th = t_resized.shape[1], t_resized.shape[0]
        
        if best_loc is None or best_score < 0.3:
            logger.debug("未检测到五角星（匹配度不足）")
            return None
        
        top_left = (sx + best_loc[0], sy + best_loc[1])
        bottom_right = (top_left[0] + best_tw, top_left[1] + best_th)
        y1, y2 = top_left[1], bottom_right[1]
        x1 = top_left[0] + tw + Config.COLOR_REGION_OFFSET_X
        x2 = x1 + Config.COLOR_REGION_WIDTH
        color_region = frame[y1:y2, x1:x2]
        
        reshaped = color_region.reshape(-1, 3)
        colors, counts = np.unique(reshaped, axis=0, return_counts=True)
        dominant_bgr = colors[np.argmax(counts)]
        dominant_rgb = tuple(int(c) for c in dominant_bgr[::-1])
        
        def color_distance(c1, c2):
            return np.linalg.norm(np.array(c1) - np.array(c2))
        
        best_name = None
        best_dist = float('inf')
        for q_name, qc in Config.QUALITY_COLORS.items():
            d = color_distance(dominant_rgb, qc)
            if d < best_dist:
                best_name = q_name
                best_dist = d
        
        if best_name:
            with stats_lock:
                star_quality_count[best_name] += 1
            # 更新 GUI 显示
            if log_window:
                log_window.update_stats_display()
            return best_name
        return None
    except Exception as e:
        logger.error(f"五角星检测异常: {e}")
        traceback.print_exc()
        return None

# -------------------- 钓鱼流程核心函数 --------------------
def check_cast_success(frame: np.ndarray) -> bool:
    roi = extract_roi(frame, *Config.CAST_SUCCESS_REGION, win_mgr.width, win_mgr.height)
    if roi is None or roi.size == 0:
        return False
    mean_bgr = np.array(cv2.mean(roi)[:3], dtype=np.float32)
    dist = np.linalg.norm(mean_bgr - Config.CAST_SUCCESS_TARGET_BGR)
    return dist <= Config.CAST_COLOR_TOLERANCE

def wait_for_bite(fishing_start_time: float) -> Tuple[bool, str]:
    trigger = NumberChangeTrigger(
        Config.NUMBER_REGION[0], Config.NUMBER_REGION[1],
        Config.NUMBER_REGION[2], Config.NUMBER_REGION[3],
        threshold=Config.NUMBER_SIMILARITY_THRESHOLD
    )
    with mss.mss() as sct:
        frame = win_mgr.capture(sct)
        trigger.set_base(frame, win_mgr.width, win_mgr.height)
    
    cast_failure_checked = False
    last_sec = -1
    while True:
        elapsed = time.time() - fishing_start_time
        
        if not cast_failure_checked and elapsed >= Config.CAST_FAILURE_CHECK_SEC:
            cast_failure_checked = True
            with mss.mss() as sct:
                frame = win_mgr.capture(sct)
            if not check_cast_success(frame):
                return False, "cast_failed"
        
        with mss.mss() as sct:
            frame = win_mgr.capture(sct)
        should_reel, sim = trigger.should_reel(frame, win_mgr.width, win_mgr.height)
        if should_reel:
            logger.info("🫧 咬钩啦！收杆！")
            return True, "bite"
        
        current_sec = int(elapsed)
        if current_sec != last_sec:
            logger.debug(f"⏳ 等待咬钩... {current_sec} 秒")
            last_sec = current_sec
        
        if elapsed >= Config.BITE_TIMEOUT:
            logger.info("⏰ 超时，未咬钩")
            return False, "timeout"
        
        time.sleep(0.05)

def reel_fish(fishing_start_time: float):
    # 收杆检测点（原代码逻辑）
    check_x = int((0.5 * win_mgr.width) + win_mgr.left + 100 + 50 * (win_mgr.width // 1800))
    check_y = int((0.9478 * win_mgr.height) + win_mgr.top)
    base_color_orange = (255, 195, 83)
    times = 0
    while True:
        try:
            color_exist = get_pixel_color_abs(check_x, check_y)
        except Exception:
            time.sleep(0.05)
            continue
        times += 1
        if is_color_in_range(base_color_orange, color_exist, tolerance=100) and times >= 3:
            break
        left_down()
        time.sleep(0.6)
        try:
            color_exist = get_pixel_color_abs(check_x, check_y)
        except Exception:
            pass
        if is_color_in_range(base_color_orange, color_exist, tolerance=100) and times >= 3:
            break
        left_up()
        time.sleep(0.3)
    left_up()
    total_time = time.time() - fishing_start_time
    logger.info(f"🐟 上鱼咯！耗时 {total_time:.2f} 秒")

def handle_bucket_full() -> str:
    logger.info("🐟 鱼桶已满，停止钓鱼！按住左键10秒并等待60秒...")
    left_down()
    time.sleep(10)
    left_up()
    time.sleep(Config.BUCKET_FULL_WAIT_SEC)
    return "bucket_full"

def auto_fish_once() -> str:
    with mss.mss() as sct:
        pre_cast_frame = win_mgr.capture(sct)
    
    f_trigger = FButtonChangeTrigger(
        *Config.F_BUTTON_REGION,
        threshold=Config.F_BUTTON_SIMILARITY_THRESHOLD,
        min_consecutive=Config.F_BUTTON_MIN_CONSECUTIVE
    )
    f_trigger.set_base(pre_cast_frame, win_mgr.width, win_mgr.height)
    
    left_down()
    logger.info("🎣 抛竿中...")
    fishing_start_time = time.time()
    time.sleep(1.0)
    
    bucket_full_detected = False
    for _ in range(5):
        with mss.mss() as sct:
            frame = win_mgr.capture(sct)
        is_full, _ = f_trigger.check_bucket_full(frame, win_mgr.width, win_mgr.height)
        if is_full:
            bucket_full_detected = True
            break
        time.sleep(0.1)
    if bucket_full_detected:
        left_up()
        return handle_bucket_full()
    
    time.sleep(random.uniform(1.0, 1.5))
    try:
        pyautogui.keyDown('a')
        time.sleep(0.05)
        pyautogui.keyUp('a')
    except Exception:
        pass
    left_up()
    
    bite_success, reason = wait_for_bite(fishing_start_time)
    if not bite_success:
        if reason == "cast_failed":
            logger.info("❌ 抛竿失败，重整方向")
            try:
                pyautogui.press('w')
                time.sleep(3)
            except Exception:
                pass
        return reason
    
    reel_fish(fishing_start_time)
    time.sleep(random.uniform(1.5, 2.5))
    left_click()
    
    with mss.mss() as sct:
        frame = win_mgr.capture(sct)
    quality = detect_star_quality(frame)
    if quality:
        logger.info(f"⭐ 品质: {quality}")
    time.sleep(1)
    return "success"

# -------------------- GUI 日志窗口（无图片） --------------------
class LogWindow:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("🦊 Vicksy")
        self.root.overrideredirect(True)
        self.root.geometry("280x300")  # 高度减小，因为去掉了图片
        self.root.attributes("-topmost", True)
        self.root.configure(bg='white')
        self.root.wm_attributes("-transparentcolor", 'white')
        
        # 拖动
        self.root.bind("<ButtonPress-1>", self.start_move)
        self.root.bind("<B1-Motion>", self.do_move)
        
        # 关闭按钮
        close_btn = tk.Button(self.root, text="×", command=self.on_close,
                              bg='white', fg='red', font=("Arial", 16, "bold"),
                              bd=0, highlightthickness=0, width=2)
        close_btn.place(relx=1.0, rely=0.0, anchor='ne')
        
        # 没有图片，直接显示标题文字
        title_label = tk.Label(self.root, text="🦊 狐狐钓鱼辅助", bg='white',
                               fg='black', font=("微软雅黑", 12, "bold"))
        title_label.pack(pady=8)
        
        # 日志文本框（保留最多10行）
        self.log_text = tk.Text(self.root, bg='black', fg='yellow',
                                font=("Segoe UI Mono", 9), height=6,
                                wrap=tk.WORD, state=tk.DISABLED)
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=(0,5))
        
        # 统计栏
        self.stats_text = tk.Text(self.root, bg='black', fg='yellow',
                                  font=("Segoe UI Mono", 9), height=1,
                                  wrap=tk.NONE, state=tk.DISABLED,
                                  relief=tk.FLAT, padx=5, pady=2)
        self.stats_text.pack(fill=tk.X, padx=5, pady=(0,5))
        
        # 状态栏
        self.status_text = tk.Text(self.root, bg='black', fg='yellow',
                                   font=("微软雅黑", 9), height=1,
                                   wrap=tk.NONE, state=tk.DISABLED,
                                   relief=tk.FLAT, padx=5, pady=2)
        self.status_text.pack(fill=tk.X, padx=5, pady=(0,5))
        
        # 配置 tags
        self.status_text.tag_configure("paused", foreground="red")
        self.status_text.tag_configure("running", foreground="green")
        self.stats_text.tag_configure("total", foreground="yellow")
        for q, color in Config.QUALITY_COLORS.items():
            self.stats_text.tag_configure(q, foreground=f"#{color[0]:02x}{color[1]:02x}{color[2]:02x}")
        
        self.log_queue = queue.Queue()
        self.running = True
        self.update_logs()
        self.update_stats_display()
        self.update_status_display()
    
    def start_move(self, event):
        self.x = event.x
        self.y = event.y
    
    def do_move(self, event):
        deltax = event.x - self.x
        deltay = event.y - self.y
        x = self.root.winfo_x() + deltax
        y = self.root.winfo_y() + deltay
        self.root.geometry(f"+{x}+{y}")
    
    def on_close(self):
        self.running = False
        self.root.destroy()
        os._exit(0)
    
    def log(self, message: str):
        self.log_queue.put(message)
    
    def update_logs(self):
        while not self.log_queue.empty():
            msg = self.log_queue.get()
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, msg + "\n")
            line_count = int(self.log_text.index('end-1c').split('.')[0])
            while line_count > 10:
                self.log_text.delete(1.0, "2.0")
                line_count -= 1
            self.log_text.config(state=tk.DISABLED)
            self.log_text.see(tk.END)
        if self.running:
            self.root.after(100, self.update_logs)
    
    def update_stats_display(self):
        with stats_lock:
            total = sum(star_quality_count.values())
            self.stats_text.config(state=tk.NORMAL)
            self.stats_text.delete(1.0, tk.END)
            self.stats_text.insert(tk.END, f"🎣{total} | ", "total")
            for q in Config.QUALITY_COLORS.keys():
                cnt = star_quality_count.get(q, 0)
                sym = "●"
                self.stats_text.insert(tk.END, sym, q)
                self.stats_text.insert(tk.END, f"{cnt} ", q)
            self.stats_text.config(state=tk.DISABLED)
    
    def update_status_display(self):
        with pause_lock:
            paused = fishing_paused
        indicator = "🔴" if paused else "🟢"
        tag = "paused" if paused else "running"
        self.status_text.config(state=tk.NORMAL)
        self.status_text.delete(1.0, tk.END)
        self.status_text.insert(tk.END, indicator, tag)
        self.status_text.insert(tk.END, " F1: 开关 | F2: 退出")
        self.status_text.config(state=tk.DISABLED)
    
    def run(self):
        self.root.mainloop()

# -------------------- 主程序入口 --------------------
def main():
    global fishing_paused, log_window
    
    if not win_mgr.find_window():
        logger.error("无法找到游戏窗口，请确保游戏已启动")
        sys.exit(1)
    
    log_window = LogWindow()
    
    # 重定向 print 到日志窗口
    class PrintRedirector:
        def write(self, text):
            if text.strip():
                if log_window:
                    log_window.log(text.strip())
                else:
                    print(text, end='')
        def flush(self):
            pass
    sys.stdout = PrintRedirector()
    sys.stderr = PrintRedirector()
    
    logger.info("🦊 狐狐附身...")
    logger.info("✅ 按 F1 开始/暂停自动钓鱼")
    logger.info("请将窗口切回至猛兽派对...")
    logger.info(f"游戏窗口分辨率: {win_mgr.width}x{win_mgr.height}")
    logger.info("面朝小河，拿起鱼竿，准备好钓饵     按 F1 请🦊狐狐附身钓鱼")
    
    def toggle_fishing(e=None):
        global fishing_paused
        with pause_lock:
            fishing_paused = not fishing_paused
        status = "⏸ 已暂停" if fishing_paused else "▶ 钓鱼中..."
        logger.info(status)
        if log_window:
            log_window.update_status_display()
    
    keyboard.add_hotkey('F1', toggle_fishing)
    
    def exit_listener():
        keyboard.wait('f2')
        logger.info("F2 按下，程序退出")
        os._exit(0)
    threading.Thread(target=exit_listener, daemon=True).start()
    
    def fishing_loop():
        global fishing_paused
        bucket_full_retry = 0
        while True:
            with pause_lock:
                paused = fishing_paused
            if paused:
                time.sleep(0.2)
                continue
            result = auto_fish_once()
            if result == "bucket_full":
                bucket_full_retry += 1
                if bucket_full_retry >= Config.BUCKET_FULL_MAX_RETRIES:
                    logger.info("多次检测到鱼桶满，程序停止")
                    break
                logger.info(f"鱼桶满检测次数: {bucket_full_retry}/{Config.BUCKET_FULL_MAX_RETRIES}")
            else:
                bucket_full_retry = 0
            time.sleep(0.5)
    
    threading.Thread(target=fishing_loop, daemon=True).start()
    
    try:
        log_window.run()
    except KeyboardInterrupt:
        pass
    finally:
        if log_window:
            log_window.running = False

if __name__ == "__main__":
    main()
