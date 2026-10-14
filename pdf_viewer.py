#!/usr/bin/env python3
"""
シンプルな PDF ビューワ (Tkinter + PyMuPDF + Pillow)

機能 / ショートカット
  単語検索            Ctrl+F  (Enter=次へ, Shift+Enter=前へ, F3 / Shift+F3, Esc で閉じる)
  拡大/縮小           Ctrl+ホイール, Ctrl++ / Ctrl+-, ツールバー
  100% に設定         Ctrl+1  (ツールバーの「100%」)
  幅に合わせる        Ctrl+0
  ページ移動          PageUp/PageDown, Home/End, ←/→, ツールバー, ページ番号入力
  表示方法            Ctrl+2 = 1ページ / Ctrl+3 = 見開き2ページ / Ctrl+4 = 1ページ目の単独表示 切替
  綴じ方向(見開き)    Ctrl+5 = 左綴じ/右綴じ 切替 (右綴じでは右ページが先、←キーが「次へ」になる)
  印刷                Ctrl+P  (ツールバーの「印刷」)。印刷ダイアログを表示
  画像として保存      Ctrl+S  (PDF と同じフォルダへ「PDF名_p001.png」のように保存)
  フルスクリーン      Ctrl+L  (Esc でも解除)。ツールバーとスクロールバーを隠し、
                      ページ全体が画面に収まる倍率へ自動調整 (切替時/表示方法の変更時のみ)
  テキスト選択/コピー ドラッグで選択, Ctrl+C (ダブルクリック=単語, トリプル=行, Ctrl+A=全選択)
  テキスト以外をドラッグ → 表示領域をスクロール

設定(表示方法・1ページ目単独・綴じ方向・フルスクリーン)は変更時に自動保存され、次回起動時に
復元されます。拡大率とウィンドウサイズは保存せず、通常モードで起動するたびに
「ページ全体が画面に収まる倍率」と「それに合わせたウィンドウサイズ」へ自動調整します。

使い方
  pip install pymupdf pillow
  python pdf_viewer.py [file.pdf]
"""
import bisect
import ctypes
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tkinter as tk
from pathlib import Path
from tkinter import ttk, filedialog, messagebox, simpledialog

try:
    import pymupdf as fitz
except ImportError:  # 古い PyMuPDF
    import fitz
from PIL import Image, ImageTk

APP_NAME = "SimplePDFViewer"          # 設定フォルダ名 (変更すると保存済みの設定は引き継がれない)
APP_TITLE = "SimplePDFViewer"        # タイトルバーに表示するアプリ名
ICON_NAME = "pdf_viewer_icon.ico"    # スクリプト(exe)と同じ場所に置く
DPI_SCALE = 96 / 72                  # 表示倍率100% = 96dpi 相当 (内部zoom = px/pt)
ZOOM_MIN, ZOOM_MAX, ZOOM_STEP = 0.2, 6.0, 1.25
PRINT_MAX_DPI = 300                  # 印刷時にページを描画する最大解像度
EDGE_ZONE = 24                       # フルスクリーン: 画面端からこの距離(px)に近づくとスクロールバーを表示
EDGE_POLL_MS = 100                   # 同: マウス位置の確認間隔
CAPTURE_DPI = 200                    # 画像保存時の解像度
PAD = 0                              # ページ周囲の余白(px) 0=余白なし
FIT_EPS = 0.999                      # 倍率の端数切り上げで1pxはみ出してスクロールが出るのを防ぐ
AUTO_FIT_RATIO = 0.8                 # 起動時の自動調整: ページ全体を画面の何割に収めるか
GAP_PT = 3                           # 見開きのページ間の隙間(pt)
BG_RGB = (128, 128, 128)
SEL_COLOR = (51, 144, 255, 90)
HIT_COLOR = (255, 230, 0, 120)
CUR_COLOR = (255, 130, 0, 150)
TEXT_FLAGS = fitz.TEXTFLAGS_RAWDICT & ~fitz.TEXT_PRESERVE_LIGATURES & ~fitz.TEXT_PRESERVE_IMAGES
LAYOUT_LABELS = {"single": "1ページ", "spread": "見開き2ページ"}
BINDING_LABELS = {"left": "左綴じ", "right": "右綴じ"}

DEFAULT_SETTINGS = {
    "view_mode": "single",      # "single" / "spread"
    "cover_alone": True,        # 見開き時に1ページ目を単独表示
    "binding": "left",          # "left"=左綴じ / "right"=右綴じ (見開き時)
    "fullscreen": False,
}


# ---------------------------------------------------------------- 設定の保存
def settings_path():
    if sys.platform == "win32":
        base = Path(os.environ.get("APPDATA") or Path.home())
    elif sys.platform == "darwin":
        base = Path.home() / "Library" / "Application Support"
    else:
        base = Path(os.environ.get("XDG_CONFIG_HOME") or Path.home() / ".config")
    return base / APP_NAME / "settings.json"


def load_settings():
    s = dict(DEFAULT_SETTINGS)
    try:
        with open(settings_path(), encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            for k, default in DEFAULT_SETTINGS.items():
                v = data.get(k)
                if isinstance(v, type(default)):
                    s[k] = v
    except (OSError, ValueError):
        pass
    if s["view_mode"] not in LAYOUT_LABELS:
        s["view_mode"] = "single"
    if s["binding"] not in BINDING_LABELS:
        s["binding"] = "left"
    return s


def resource_path(name):
    """スクリプトと同じフォルダ、または PyInstaller で同梱したファイルのパス"""
    base = Path(getattr(sys, "_MEIPASS", Path(__file__).resolve().parent))
    return base / name


def set_window_icon(root):
    """タイトルバー/タスクバーのアイコンを設定する (見つからない場合は既定のまま)"""
    ico = resource_path(ICON_NAME)
    if not ico.is_file():
        return
    try:
        if sys.platform == "win32":
            root.iconbitmap(default=str(ico))
        else:  # .ico は Windows 専用なので、他OSでは画像として設定
            img = Image.open(ico)
            root._icon_photo = ImageTk.PhotoImage(img.convert("RGBA"))
            root.iconphoto(True, root._icon_photo)
    except Exception:
        pass


def char_kind(ch):
    """ダブルクリックで単語範囲を決めるための文字種"""
    o = ord(ch)
    if ch.isascii() and (ch.isalnum() or ch == "_"):
        return "a"
    if 0x3040 <= o <= 0x309F:
        return "hira"
    if 0x30A0 <= o <= 0x30FF:
        return "kata"
    if 0x4E00 <= o <= 0x9FFF:
        return "kanji"
    return ("o", ch)


if sys.platform == "win32":
    from ctypes import wintypes

    PD_NOSELECTION = 0x4
    PD_PAGENUMS = 0x2
    PD_RETURNDC = 0x100
    PD_USEDEVMODECOPIESANDCOLLATE = 0x40000
    PD_HIDEPRINTTOFILE = 0x100000
    HORZRES, VERTRES = 8, 10

    class _PRINTDLGW(ctypes.Structure):
        _pack_ = 1 if ctypes.sizeof(ctypes.c_void_p) == 4 else 8   # 32bit版は1バイト詰め
        _fields_ = [
            ("lStructSize", wintypes.DWORD), ("hwndOwner", ctypes.c_void_p),
            ("hDevMode", ctypes.c_void_p), ("hDevNames", ctypes.c_void_p),
            ("hDC", ctypes.c_void_p), ("Flags", wintypes.DWORD),
            ("nFromPage", wintypes.WORD), ("nToPage", wintypes.WORD),
            ("nMinPage", wintypes.WORD), ("nMaxPage", wintypes.WORD),
            ("nCopies", wintypes.WORD), ("hInstance", ctypes.c_void_p),
            ("lCustData", wintypes.LPARAM), ("lpfnPrintHook", ctypes.c_void_p),
            ("lpfnSetupHook", ctypes.c_void_p), ("lpPrintTemplateName", wintypes.LPCWSTR),
            ("lpSetupTemplateName", wintypes.LPCWSTR), ("hPrintTemplate", ctypes.c_void_p),
            ("hSetupTemplate", ctypes.c_void_p),
        ]

    class _DOCINFOW(ctypes.Structure):
        _fields_ = [("cbSize", ctypes.c_int), ("lpszDocName", wintypes.LPCWSTR),
                    ("lpszOutput", wintypes.LPCWSTR), ("lpszDatatype", wintypes.LPCWSTR),
                    ("fwType", wintypes.DWORD)]

    _comdlg32 = ctypes.WinDLL("comdlg32", use_last_error=True)
    _gdi32 = ctypes.WinDLL("gdi32", use_last_error=True)
    _kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    _user32 = ctypes.WinDLL("user32", use_last_error=True)
    _comdlg32.PrintDlgW.argtypes = [ctypes.POINTER(_PRINTDLGW)]
    _comdlg32.PrintDlgW.restype = wintypes.BOOL
    _gdi32.StartDocW.argtypes = [ctypes.c_void_p, ctypes.POINTER(_DOCINFOW)]
    _gdi32.StartDocW.restype = ctypes.c_int
    for _f in (_gdi32.StartPage, _gdi32.EndPage, _gdi32.EndDoc, _gdi32.AbortDoc, _gdi32.DeleteDC):
        _f.argtypes = [ctypes.c_void_p]
        _f.restype = ctypes.c_int
    _gdi32.GetDeviceCaps.argtypes = [ctypes.c_void_p, ctypes.c_int]
    _gdi32.GetDeviceCaps.restype = ctypes.c_int
    _kernel32.GlobalFree.argtypes = [ctypes.c_void_p]
    _kernel32.GlobalFree.restype = ctypes.c_void_p
    _user32.GetParent.argtypes = [ctypes.c_void_p]
    _user32.GetParent.restype = ctypes.c_void_p

    class _MONITORINFO(ctypes.Structure):
        _fields_ = [("cbSize", wintypes.DWORD), ("rcMonitor", wintypes.RECT),
                    ("rcWork", wintypes.RECT), ("dwFlags", wintypes.DWORD)]

    _user32.MonitorFromPoint.argtypes = [wintypes.POINT, wintypes.DWORD]
    _user32.MonitorFromPoint.restype = ctypes.c_void_p
    _user32.GetMonitorInfoW.argtypes = [ctypes.c_void_p, ctypes.POINTER(_MONITORINFO)]
    _user32.GetMonitorInfoW.restype = wintypes.BOOL

    def win_monitor_rect(x=None, y=None):
        """点(x, y)があるモニタの範囲 (left, top, 幅, 高さ)。x が None ならプライマリモニタ"""
        flag = 2 if x is not None else 1       # NEAREST / PRIMARY
        hmon = _user32.MonitorFromPoint(wintypes.POINT(int(x or 0), int(y or 0)), flag)
        if not hmon:
            return None
        mi = _MONITORINFO()
        mi.cbSize = ctypes.sizeof(mi)
        if not _user32.GetMonitorInfoW(hmon, ctypes.byref(mi)):
            return None
        r = mi.rcMonitor
        return r.left, r.top, r.right - r.left, r.bottom - r.top

    def win_print_dialog(hwnd, first, last, from_page, to_page):
        """Windows標準の印刷ダイアログを表示する。
        OKなら (hDC, 開始ページ, 終了ページ) (ページ番号は1始まり)、キャンセルなら None"""
        last = min(last, 65535)
        pd = _PRINTDLGW()
        pd.lStructSize = ctypes.sizeof(pd)
        pd.hwndOwner = hwnd
        pd.Flags = (PD_RETURNDC | PD_NOSELECTION | PD_USEDEVMODECOPIESANDCOLLATE
                    | PD_HIDEPRINTTOFILE)
        pd.nMinPage, pd.nMaxPage = first, last
        pd.nFromPage, pd.nToPage = min(from_page, last), min(to_page, last)
        pd.nCopies = 1
        if not _comdlg32.PrintDlgW(ctypes.byref(pd)):
            return None            # キャンセル (エラー時もここ)
        for h in (pd.hDevMode, pd.hDevNames):
            if h:
                _kernel32.GlobalFree(h)
        if pd.Flags & PD_PAGENUMS:
            return pd.hDC, pd.nFromPage, pd.nToPage
        return pd.hDC, first, last


class PdfViewer:
    def __init__(self, root, path=None):
        self.root = root
        self.settings = load_settings()
        self.doc = None
        self.path = None

        # 表示中のページ(1ページ or 見開き)
        self.view_pages = []      # 表示中のページ番号(0始まり)
        self.page_no = 0          # 表示中の先頭ページ
        self.view_layout = []     # (page, x_pt, y_pt, w_pt, h_pt)
        self.view_w = self.view_h = 0.0

        # 設定
        self.view_mode = self.settings["view_mode"]
        self.cover_alone = self.settings["cover_alone"]
        self.binding = self.settings["binding"]
        self.fit_mode = False
        self.zoom = DPI_SCALE
        self._startup_fit = True      # 通常モードで最初に文書を表示するとき自動調整する
        self.fullscreen = False
        self.windowed_geometry = ""

        # 表示領域のテキスト情報 (見開き全体の座標系, pt)
        self.chars = []   # (文字, (x0,y0,x1,y1), 行ID)
        self.lines = []   # 行ID -> (x0,y0,x1,y1)

        # 選択 / ドラッグ
        self.sel = None
        self.anchor = None
        self.drag_mode = None    # None / "select" / "pan"
        self._cursor = None

        # 検索
        self.query = None
        self.hit_cache = {}
        self.cur_hit = None      # (page, index)
        self.search_visible = False

        # 描画
        self.photo = None
        self.img_id = None
        self.ox = self.oy = 0
        self.W = self.H = 1
        self._imgs = {}
        self.last_flip = 0.0
        self._last_w = 0
        self._fit_job = None
        self._save_job = None
        self._toast_job = None
        self._fs_job = None
        self._fs_fit_pending = False   # フルスクリーン用の自動調整待ち
        self._pre_fs = None            # フルスクリーン前の (fit_mode, zoom)
        # 文書全体(全ページ)を対象にした垂直スクロールバー用の情報
        self.page_sizes = []           # 各ページの (幅pt, 高さpt)
        self.views = []                # ビュー(1ページ or 見開き)ごとのページ番号リスト
        self.page_to_view = []
        self.view_off_pt = []          # 各ビューの先頭位置 (文書先頭からの距離, pt)
        self.total_pt = 0.0
        self.cur_view = 0
        self._doc_serial = 0
        self._views_key = None
        self._vs_range = (0.0, 1.0)
        self._pending_doc_y = None
        self._doc_scroll_job = None
        # フルスクリーン時、画面端でスクロールバーを出す
        self._poll_job = None
        self._sb_drag = False
        self._vs_shown = False
        self._hs_shown = False

        self._build_ui()
        self._apply_initial_window()
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        if path:
            self.open_pdf(path)
        else:
            root.after(100, self.ask_open)

    # ------------------------------------------------------------------ UI
    def _build_ui(self):
        root = self.root
        root.title(APP_TITLE)
        set_window_icon(root)

        # 上部: ツールバー + 検索バー
        self.top = ttk.Frame(root)
        self.top.pack(side="top", fill="x")
        self.top.columnconfigure(0, weight=1)
        bar = self.toolbar = ttk.Frame(self.top, padding=4)
        bar.grid(row=0, column=0, sticky="ew")

        def sep():
            ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=6)

        ttk.Button(bar, text="開く", width=5, command=self.ask_open).pack(side="left")
        sep()
        ttk.Button(bar, text="◀", width=3, command=self.prev_view).pack(side="left")
        self.page_var = tk.StringVar()
        self.page_entry = ttk.Entry(bar, textvariable=self.page_var, width=7, justify="right")
        self.page_entry.pack(side="left", padx=2)
        self.page_entry.bind("<Return>", self._on_page_entry)
        self.page_total = ttk.Label(bar, text="/ 0", width=7)
        self.page_total.pack(side="left")
        ttk.Button(bar, text="▶", width=3, command=self.next_view).pack(side="left")
        sep()
        ttk.Button(bar, text="－", width=3,
                   command=lambda: self.zoom_by(1 / ZOOM_STEP)).pack(side="left")
        self.zoom_label = ttk.Label(bar, text="100%", width=6, anchor="center")
        self.zoom_label.pack(side="left")
        ttk.Button(bar, text="＋", width=3,
                   command=lambda: self.zoom_by(ZOOM_STEP)).pack(side="left")
        ttk.Button(bar, text="100%", width=5, command=self.zoom_100).pack(side="left", padx=(6, 0))
        ttk.Button(bar, text="幅に合わせる", command=self.fit_width).pack(side="left", padx=2)
        sep()
        self.layout_combo = ttk.Combobox(bar, state="readonly", width=12,
                                         values=list(LAYOUT_LABELS.values()))
        self.layout_combo.pack(side="left")
        self.layout_combo.bind("<<ComboboxSelected>>", self._on_layout_selected)
        self.binding_combo = ttk.Combobox(bar, state="readonly", width=7,
                                          values=list(BINDING_LABELS.values()))
        self.binding_combo.pack(side="left", padx=(4, 0))
        self.binding_combo.bind("<<ComboboxSelected>>", self._on_binding_selected)
        self.cover_var = tk.BooleanVar(value=self.cover_alone)
        self.cover_check = ttk.Checkbutton(bar, text="1ページ目単独",
                                           variable=self.cover_var, command=self._on_cover_toggle)
        self.cover_check.pack(side="left", padx=6)
        sep()
        ttk.Button(bar, text="画像保存", command=self.save_capture).pack(side="left")
        ttk.Button(bar, text="印刷", width=5, command=self.print_document).pack(side="left", padx=2)
        ttk.Button(bar, text="検索", width=5, command=self.open_search).pack(side="left", padx=2)
        ttk.Button(bar, text="全画面", width=6,
                   command=self.toggle_fullscreen).pack(side="left")

        sb = self.search_bar = ttk.Frame(self.top, padding=(4, 2))
        sb.grid(row=1, column=0, sticky="ew")
        ttk.Label(sb, text="検索:").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(sb, textvariable=self.search_var, width=32)
        self.search_entry.pack(side="left", padx=4)
        ttk.Button(sb, text="↑ 前へ", command=lambda: self.find(-1)).pack(side="left")
        ttk.Button(sb, text="↓ 次へ", command=lambda: self.find(1)).pack(side="left", padx=2)
        self.search_info = ttk.Label(sb, text="")
        self.search_info.pack(side="left", padx=8)
        ttk.Button(sb, text="✕", width=3, command=self.close_search).pack(side="right")
        sb.grid_remove()
        self.search_var.trace_add("write", self._on_search_change)
        self.search_entry.bind("<Return>", lambda e: self.find(1))
        self.search_entry.bind("<Shift-Return>", lambda e: self.find(-1))

        # 本体 (canvas + scrollbars)
        self.body = ttk.Frame(root)
        self.body.pack(side="top", fill="both", expand=True)
        c = self.canvas = tk.Canvas(self.body, bg="#808080", highlightthickness=0,
                                    xscrollincrement=30, yscrollincrement=30)
        # 垂直スクロールバーは「現在のページ」ではなく文書全体の位置を表す
        self.vscroll = vs = ttk.Scrollbar(self.body, orient="vertical", command=self._on_vscroll)
        self.hscroll = hs = ttk.Scrollbar(self.body, orient="horizontal", command=c.xview)
        c.configure(xscrollcommand=hs.set, yscrollcommand=lambda *a: self._update_vscroll())
        for bar in (vs, hs):   # つまみのドラッグ中は(フルスクリーンでも)隠さない
            bar.bind("<ButtonPress-1>", lambda e: setattr(self, "_sb_drag", True), add="+")
            bar.bind("<ButtonRelease-1>", lambda e: setattr(self, "_sb_drag", False), add="+")
        self.body.rowconfigure(0, weight=1)
        self.body.columnconfigure(0, weight=1)
        c.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        hs.grid(row=1, column=0, sticky="ew")

        # 一時メッセージ (フルスクリーンでもツールバー無しで見えるようにcanvas上に出す)
        self.toast_label = tk.Label(c, bg="#202020", fg="white", padx=12, pady=5)

        # マウス
        c.bind("<Configure>", self.on_canvas_configure)
        c.bind("<ButtonPress-1>", lambda e: self.on_press(e, 1))
        c.bind("<Double-ButtonPress-1>", lambda e: self.on_press(e, 2))
        c.bind("<Triple-ButtonPress-1>", lambda e: self.on_press(e, 3))
        c.bind("<B1-Motion>", self.on_drag)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<Motion>", self.on_motion)
        c.bind("<MouseWheel>", self.on_wheel)
        c.bind("<Button-4>", self.on_wheel)   # Linux
        c.bind("<Button-5>", self.on_wheel)

        # キーボード
        mods = ["Control"] + (["Command"] if sys.platform == "darwin" else [])
        for m in mods:
            root.bind(f"<{m}-f>", self.open_search)
            root.bind(f"<{m}-F>", self.open_search)
            root.bind(f"<{m}-o>", lambda e: self.ask_open())
            root.bind(f"<{m}-s>", self.save_capture)
            root.bind(f"<{m}-p>", self.print_document)
            root.bind(f"<{m}-P>", self.print_document)
            root.bind(f"<{m}-l>", self.toggle_fullscreen)
            root.bind(f"<{m}-L>", self.toggle_fullscreen)
            root.bind(f"<{m}-Key-1>", lambda e: self.zoom_100())
            root.bind(f"<{m}-Key-2>", lambda e: self.set_view_mode("single"))
            root.bind(f"<{m}-Key-3>", lambda e: self.set_view_mode("spread"))
            root.bind(f"<{m}-Key-4>", lambda e: self.set_cover_alone(not self.cover_alone))
            root.bind(f"<{m}-Key-5>",
                      lambda e: self.set_binding("right" if self.binding == "left" else "left"))
            c.bind(f"<{m}-c>", self.copy_selection)
            c.bind(f"<{m}-C>", self.copy_selection)
            c.bind(f"<{m}-a>", self.select_all)
            c.bind(f"<{m}-A>", self.select_all)
            for k in ("plus", "equal", "KP_Add"):
                c.bind(f"<{m}-{k}>", lambda e: self.zoom_by(ZOOM_STEP))
            for k in ("minus", "KP_Subtract"):
                c.bind(f"<{m}-{k}>", lambda e: self.zoom_by(1 / ZOOM_STEP))
            c.bind(f"<{m}-Key-0>", lambda e: self.fit_width())
        root.bind("<Escape>", self.on_escape)
        c.bind("<F3>", lambda e: self.find(1))
        c.bind("<Shift-F3>", lambda e: self.find(-1))
        c.bind("<Prior>", lambda e: self.prev_view())
        c.bind("<Next>", lambda e: self.next_view())
        c.bind("<Home>", lambda e: self.goto_page(0))
        c.bind("<End>", lambda e: self.goto_page(len(self.doc) - 1) if self.doc else None)
        c.bind("<Up>", lambda e: self.scroll_or_flip(1, 1))
        c.bind("<Down>", lambda e: self.scroll_or_flip(-1, 1))
        c.bind("<Left>", lambda e: self.key_horizontal(-1))
        c.bind("<Right>", lambda e: self.key_horizontal(1))
        c.focus_set()

        self._sync_view_widgets()

    def _sync_view_widgets(self):
        self.layout_combo.set(LAYOUT_LABELS[self.view_mode])
        self.cover_var.set(self.cover_alone)
        self.binding_combo.set(BINDING_LABELS[self.binding])
        spread = self.view_mode == "spread"
        self.binding_combo.configure(state="readonly" if spread else "disabled")
        self.cover_check.state(["!disabled"] if spread else ["disabled"])

    def toast(self, text, ms=2500):
        self.toast_label.config(text=text)
        self.toast_label.place(relx=0.5, rely=1.0, anchor="s", y=-16)
        if self._toast_job:
            self.root.after_cancel(self._toast_job)
        self._toast_job = self.root.after(ms, self.toast_label.place_forget)

    # ------------------------------------------------------------- 設定の保存/復元
    def _apply_initial_window(self):
        self.root.geometry("1280x860")   # 文書を開くと、ページに合わせて自動調整される
        if self.settings["fullscreen"]:
            self.set_fullscreen(True)
            self._pre_fs = None          # 通常モードに戻ったときは自動調整する

    def save_settings(self):
        if self._save_job:
            self.root.after_cancel(self._save_job)
            self._save_job = None
        data = {
            "view_mode": self.view_mode,
            "cover_alone": self.cover_alone,
            "binding": self.binding,
            "fullscreen": self.fullscreen,
        }
        p = settings_path()
        try:
            p.parent.mkdir(parents=True, exist_ok=True)
            tmp = p.with_suffix(".tmp")
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            os.replace(tmp, p)
        except OSError:
            pass

    def schedule_save(self):
        if self._save_job:
            self.root.after_cancel(self._save_job)
        self._save_job = self.root.after(600, self.save_settings)

    def on_close(self):
        self.save_settings()
        self.root.destroy()

    # ------------------------------------------------------------- フルスクリーン
    def toggle_fullscreen(self, _e=None):
        self.set_fullscreen(not self.fullscreen)
        return "break"

    def _window_monitor_rect(self):
        """(Windows) ウィンドウの中心があるモニタの範囲 (left, top, 幅, 高さ)"""
        root = self.root
        if root.winfo_ismapped():
            cx = root.winfo_rootx() + root.winfo_width() // 2
            cy = root.winfo_rooty() + root.winfo_height() // 2
        else:   # 起動直後: 保存されていたウィンドウ位置から判断する
            m = re.fullmatch(r"(\d+)x(\d+)([+-]-?\d+)([+-]-?\d+)", self.windowed_geometry or "")
            if not m:
                return win_monitor_rect()
            cx = int(m.group(3)[1:]) + int(m.group(1)) // 2
            cy = int(m.group(4)[1:]) + int(m.group(2)) // 2
        return win_monitor_rect(cx, cy)

    def _apply_fullscreen_window(self, on):
        """ウィンドウを、いま表示されているモニタ全体に広げる/元に戻す。
        Windows では Tk の -fullscreen がマルチモニタで別のモニタに出ることがあるため、
        モニタの範囲を取得して枠なしウィンドウをそこに配置する。他のOSは -fullscreen を使う"""
        if on:
            rect = self._window_monitor_rect() if sys.platform == "win32" else None
            self._fs_manual = rect is not None
            if rect:
                x, y, w, h = rect
                self.root.overrideredirect(True)
                self.root.geometry(f"{w}x{h}+{x}+{y}")
                self.root.lift()
                self.root.focus_force()
            else:
                self.root.attributes("-fullscreen", True)
        elif getattr(self, "_fs_manual", False):
            self.root.overrideredirect(False)
            self._fs_manual = False
        else:
            self.root.attributes("-fullscreen", False)

    def set_fullscreen(self, on):
        if on == self.fullscreen:
            return
        if on:
            if self.root.winfo_ismapped():
                self.windowed_geometry = self.root.geometry()
            self._pre_fs = (self.fit_mode, self.zoom)
            self.toolbar.grid_remove()
            self.vscroll.grid_remove()
            self.hscroll.grid_remove()
            self.fullscreen = True
            self._start_edge_poll()
            self._apply_fullscreen_window(True)
            self._update_top()
            # ウィンドウが画面サイズになってから、ページ全体が収まる倍率に調整する
            self._fs_fit_pending = True
            self._schedule_fs_fit(250)
        else:
            self.fullscreen = False
            self._fs_fit_pending = False
            self._apply_fullscreen_window(False)
            self.toolbar.grid()
            self._stop_edge_poll()
            self.vscroll.grid(row=0, column=1, sticky="ns")
            self.hscroll.grid(row=1, column=0, sticky="ew")
            self._update_top()
            if self._startup_fit and self.view_pages:
                # フルスクリーンで起動した場合: 通常モードで初めて表示するときに自動調整
                self._startup_fit = False
                self._pre_fs = None
                self._auto_window_fit(self.view_w, self.view_h, len(self.view_pages))
                self.render()
            else:
                if self.windowed_geometry:
                    self.root.geometry(self.windowed_geometry)
                if self._pre_fs:
                    self.fit_mode, self.zoom = self._pre_fs   # 元の倍率設定に戻す
                    self._pre_fs = None
                if self.view_pages:
                    if self.fit_mode:
                        self._schedule_refit()
                    else:
                        self.render()
        self.canvas.focus_set()
        self.save_settings()
        if on:
            self.toast("フルスクリーン (Ctrl+L または Esc で解除)", 2500)

    # ------------------------------------------------------------- 文書全体の垂直スクロールバー
    def _rebuild_views(self):
        """全ページを(1ページ or 見開き)のビューに分け、文書全体の長さを求める"""
        n_pages = len(self.doc)
        self.views, self.page_to_view = [], [0] * n_pages
        n = 0
        while n < n_pages:
            pages = self.view_pages_for(n)
            for p in pages:
                self.page_to_view[p] = len(self.views)
            self.views.append(pages)
            n = pages[-1] + 1
        self.view_off_pt, y = [], 0.0
        for pages in self.views:
            self.view_off_pt.append(y)
            y += max(self.page_sizes[p][1] for p in pages)
        self.total_pt = y
        self._views_key = (self._doc_serial, self.view_mode, self.cover_alone)

    def _current_doc_y(self):
        """表示領域の上端の、文書先頭からの位置(pt)"""
        if not self.view_pages:
            return 0.0
        top_px = max(0.0, self.canvas.canvasy(0) - self.oy)
        return self.view_off_pt[self.cur_view] + top_px / self.zoom

    def _update_vscroll(self):
        """表示中の範囲を、文書全体に対する割合としてスクロールバーに反映する"""
        if not (self.doc and self.view_pages and self.photo and self.total_pt > 0):
            self._vs_range = (0.0, 1.0)
            self.vscroll.set(0.0, 1.0)
            return
        z, c = self.zoom, self.canvas
        off = self.view_off_pt[self.cur_view]
        view_h = max(self.page_sizes[p][1] for p in self.views[self.cur_view])
        top = max(0.0, c.canvasy(0) - self.oy) / z
        bot = min(view_h, max(0.0, c.canvasy(c.winfo_height()) - self.oy) / z)
        lo = min(1.0, (off + top) / self.total_pt)
        hi = min(1.0, max(lo, (off + bot) / self.total_pt))
        self._vs_range = (lo, hi)
        self.vscroll.set(lo, hi)

    def _on_vscroll(self, *args):
        """スクロールバー操作 (つまみのドラッグ / 矢印 / 空白部クリック)"""
        if not self.view_pages:
            return
        base = self._pending_doc_y if self._pending_doc_y is not None else self._current_doc_y()
        if args[0] == "moveto":
            target = float(args[1]) * self.total_pt
        else:
            n = int(float(args[1]))
            step_px = 30 if args[2] == "units" else self.canvas.winfo_height() * 0.9
            target = base + n * step_px / self.zoom
        self._pending_doc_y = target
        if not self._doc_scroll_job:    # ドラッグ中の連続イベントは最後の位置だけ反映する
            self._doc_scroll_job = self.root.after_idle(self._apply_doc_scroll)

    def _apply_doc_scroll(self):
        self._doc_scroll_job = None
        d, self._pending_doc_y = self._pending_doc_y, None
        if d is None or not self.view_pages:
            return
        d = max(0.0, min(d, self.total_pt - 1e-6))
        v = max(0, min(bisect.bisect_right(self.view_off_pt, d) - 1, len(self.views) - 1))
        if v != self.cur_view:
            self.show_page(self.views[v][0], None)
        inner_px = (d - self.view_off_pt[v]) * self.zoom
        self.canvas.yview_moveto((self.oy + inner_px) / self.H)
        self._update_vscroll()

    # ------------------------------------------------------------- フルスクリーン: 画面端でスクロールバー表示
    def _start_edge_poll(self):
        self._vs_shown = self._hs_shown = False
        if not self._poll_job:
            self._poll_job = self.root.after(EDGE_POLL_MS, self._poll_edges)

    def _stop_edge_poll(self):
        if self._poll_job:
            self.root.after_cancel(self._poll_job)
            self._poll_job = None
        self.vscroll.place_forget()
        self.hscroll.place_forget()
        self._vs_shown = self._hs_shown = False

    def _poll_edges(self):
        self._poll_job = None
        if not self.fullscreen:
            return
        try:
            c = self.canvas
            px, py = self.root.winfo_pointerxy()
            x, y = px - c.winfo_rootx(), py - c.winfo_rooty()
            cw, ch = c.winfo_width(), c.winfo_height()
            inside = 0 <= x <= cw and 0 <= y <= ch
            v_scrollable = (self._vs_range[1] - self._vs_range[0]) < 0.9999   # 全体が表示されていれば不要
            xlo, xhi = c.xview()
            h_scrollable = not (xlo <= 0 and xhi >= 1)
            zone_v = EDGE_ZONE + (self.vscroll.winfo_reqwidth() if self._vs_shown else 0)
            zone_h = EDGE_ZONE + (self.hscroll.winfo_reqheight() if self._hs_shown else 0)
            want_v = v_scrollable and ((inside and x >= cw - zone_v) or (self._sb_drag and self._vs_shown))
            want_h = h_scrollable and ((inside and y >= ch - zone_h) or (self._sb_drag and self._hs_shown))
            if want_v != self._vs_shown:
                self._vs_shown = want_v
                if want_v:
                    self.vscroll.place(in_=self.body, relx=1.0, rely=0.0, relheight=1.0, anchor="ne")
                    self.vscroll.lift()
                else:
                    self.vscroll.place_forget()
            if want_h != self._hs_shown:
                self._hs_shown = want_h
                if want_h:
                    self.hscroll.place(in_=self.body, relx=0.0, rely=1.0, relwidth=1.0, anchor="sw")
                    self.hscroll.lift()
                else:
                    self.hscroll.place_forget()
        except tk.TclError:
            pass
        self._poll_job = self.root.after(EDGE_POLL_MS, self._poll_edges)

    def _update_top(self):
        """上部フレームは、中身(ツールバー/検索バー)がある時だけ表示する。
        中身が空のgridフレームは直前の高さを保持して空白の帯になってしまうため、
        フルスクリーン中で検索バーも無い時はフレームごと取り除く。"""
        show = (not self.fullscreen) or self.search_visible
        if show and not self.top.winfo_manager():
            self.top.pack(side="top", fill="x", before=self.body)
        elif not show and self.top.winfo_manager():
            self.top.pack_forget()

    def _eff_width(self, w, npages):
        """単独表示のページ(見開きの1ページ目など)は、見開きと同じ倍率になるよう2ページ幅で扱う"""
        if self.view_mode == "spread" and npages == 1 and len(self.doc) > 1:
            return w * 2 + GAP_PT
        return w

    def _auto_window_fit(self, view_w, view_h, npages):
        """ページ全体が画面に収まる倍率を決め、ウィンドウをそのサイズに合わせる(通常モード用)"""
        root = self.root
        root.update_idletasks()
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        tb_h = self.toolbar.winfo_reqheight()
        vs_w = self.vscroll.winfo_reqwidth()
        hs_h = self.hscroll.winfo_reqheight()
        w = self._eff_width(view_w, npages)
        # ページ表示部分が画面の AUTO_FIT_RATIO (80%) に収まる倍率
        z = min(sw * AUTO_FIT_RATIO / max(w, 1.0), sh * AUTO_FIT_RATIO / max(view_h, 1.0))
        self.zoom = max(ZOOM_MIN, min(ZOOM_MAX, z))
        self.fit_mode = False
        # ウィンドウはページ(余白なし)+ツールバー/スクロールバーの大きさ。
        # ツールバーが切れてしまう場合は、全部表示される幅まで広げる(ページは中央、左右は余白になる)
        win_w = max(math.ceil(w * self.zoom) + vs_w, self.toolbar.winfo_reqwidth())
        win_h = math.ceil(view_h * self.zoom) + tb_h + hs_h
        win_w = min(win_w, sw)
        win_h = min(win_h, sh)
        x = max(0, (sw - win_w) // 2)
        y = max(0, (sh - win_h) // 2 - 20)
        root.geometry(f"{win_w}x{win_h}+{x}+{y}")

    def _fit_all_zoom(self):
        """ページ全体(縦横とも)が画面に収まる倍率"""
        cw = max(self.canvas.winfo_width(), 200)
        ch = max(self.canvas.winfo_height(), 200)
        w = self._eff_width(self.view_w, len(self.view_pages))
        z = min(cw / max(w, 1.0), ch / max(self.view_h, 1.0)) * FIT_EPS
        return max(ZOOM_MIN, min(ZOOM_MAX, z))

    def _schedule_fs_fit(self, ms=150):
        if self._fs_job:
            self.root.after_cancel(self._fs_job)
        self._fs_job = self.root.after(ms, self._apply_fs_fit)

    def _apply_fs_fit(self):
        self._fs_job = None
        if not self.fullscreen:
            self._fs_fit_pending = False
            return
        if not (self._fs_fit_pending and self.view_pages):
            return   # 文書が開かれるまで待つ
        self._fs_fit_pending = False
        self.fit_mode = False
        z = self._fit_all_zoom()
        if abs(z - self.zoom) > 1e-3:
            self.zoom = z
            self.render()
        self.canvas.xview_moveto(0)
        self.canvas.yview_moveto(0)

    def on_escape(self, _e=None):
        if self.search_visible:
            self.close_search()
        elif self.fullscreen:
            self.set_fullscreen(False)

    # ------------------------------------------------------------- 文書
    def ask_open(self):
        path = filedialog.askopenfilename(filetypes=[("PDF", "*.pdf"), ("All files", "*.*")])
        if path:
            self.open_pdf(path)

    def open_pdf(self, path):
        try:
            doc = fitz.open(path)
        except Exception as ex:
            messagebox.showerror("エラー", f"開けませんでした:\n{ex}")
            return
        if doc.needs_pass:
            pw = simpledialog.askstring("パスワード", "パスワードを入力してください:",
                                        show="*", parent=self.root)
            if not pw or not doc.authenticate(pw):
                messagebox.showerror("エラー", "パスワードが正しくありません。")
                return
        if len(doc) == 0:
            messagebox.showerror("エラー", "ページがありません。")
            return
        if self.doc:
            self.doc.close()
        self.doc = doc
        self.path = str(path)
        self.page_sizes = [(r.width, r.height) for r in (doc[i].rect for i in range(len(doc)))]
        self._doc_serial += 1
        self._pending_doc_y = None
        self.view_pages = []
        self.page_no = 0
        self.hit_cache.clear()
        self.cur_hit = None
        self.root.title(f"{Path(path).name} - {APP_TITLE}")
        self.page_total.config(text=f"/ {len(doc)}")
        self.root.update_idletasks()
        if self._startup_fit and not self.fullscreen:
            # 通常モードの起動: 前回の倍率/サイズは使わず、ページ全体が収まるよう毎回自動調整
            self._startup_fit = False
            pages = self.view_pages_for(0)
            _, w, h = self.make_layout(pages)
            self._auto_window_fit(w, h, len(pages))
        self.show_page(0)
        self.canvas.focus_set()

    # ------------------------------------------------------------- 表示ページ(ビュー)
    def view_pages_for(self, n):
        """ページ n を含むビュー(1ページ or 見開き)のページ番号リスト"""
        total = len(self.doc)
        if self.view_mode == "single":
            return [n]
        if self.cover_alone:
            if n == 0:
                return [0]
            s = 1 + ((n - 1) // 2) * 2
        else:
            s = (n // 2) * 2
        return [p for p in (s, s + 1) if p < total]

    def make_layout(self, pages):
        """layout は読み順(ページ順)で返す。右綴じの見開きでは左右の配置だけ入れ替える"""
        sizes = [(pno, self.doc[pno].rect.width, self.doc[pno].rect.height) for pno in pages]
        order = sizes[::-1] if (len(sizes) > 1 and self.binding == "right") else sizes
        pos, x = {}, 0.0
        for pno, w, _ in order:
            pos[pno] = x
            x += w + GAP_PT
        layout = [(pno, pos[pno], 0.0, w, h) for pno, w, h in sizes]
        return layout, x - GAP_PT, max(h for _, _, h in sizes)

    def load_text(self):
        self.chars, self.lines = [], []
        for pno, xo, yo, _, _ in self.view_layout:
            d = self.doc[pno].get_text("rawdict", flags=TEXT_FLAGS)
            for b in d["blocks"]:
                if b.get("type") != 0:
                    continue
                for ln in b["lines"]:
                    start = len(self.chars)
                    lid = len(self.lines)
                    for sp in ln["spans"]:
                        for ch in sp["chars"]:
                            x0, y0, x1, y1 = ch["bbox"]
                            self.chars.append((ch["c"], (x0 + xo, y0 + yo, x1 + xo, y1 + yo), lid))
                    if len(self.chars) > start:
                        x0, y0, x1, y1 = ln["bbox"]
                        self.lines.append((x0 + xo, y0 + yo, x1 + xo, y1 + yo))

    def show_page(self, n, scroll="top"):
        if not self.doc:
            return
        if self._views_key != (self._doc_serial, self.view_mode, self.cover_alone):
            self._rebuild_views()
        pages = self.view_pages_for(max(0, min(n, len(self.doc) - 1)))
        self.view_pages = pages
        self.page_no = pages[0]
        self.cur_view = self.page_to_view[self.page_no]
        self.view_layout, self.view_w, self.view_h = self.make_layout(pages)
        if self.fullscreen and self._fs_fit_pending:
            self.fit_mode = False
            self.zoom = self._fit_all_zoom()
            self._schedule_fs_fit()
        elif self.fit_mode:
            self.zoom = self._fit_zoom()
        self.sel = None
        self.load_text()
        self.render()
        self.page_var.set("-".join(str(p + 1) for p in (pages[0], pages[-1])) if len(pages) > 1
                          else str(pages[0] + 1))
        if scroll == "top":
            self.canvas.yview_moveto(0)
        elif scroll == "bottom":
            self.canvas.yview_moveto(1)
        self.update_search_info()

    def goto_page(self, n):
        if not self.doc:
            return
        n = max(0, min(n, len(self.doc) - 1))
        if self.view_pages_for(n)[0] != self.page_no:
            self.show_page(n, "top")

    def next_view(self):
        if self.doc and self.view_pages and self.view_pages[-1] < len(self.doc) - 1:
            self.show_page(self.view_pages[-1] + 1, "top")

    def prev_view(self, scroll="top"):
        if self.doc and self.page_no > 0:
            self.show_page(self.page_no - 1, scroll)

    def _on_page_entry(self, _e):
        m = re.search(r"\d+", self.page_var.get())
        if self.doc:
            n = int(m.group()) - 1 if m else self.page_no
            n = max(0, min(n, len(self.doc) - 1))
            if self.view_pages_for(n)[0] == self.page_no:
                self.show_page(self.page_no, None)   # 表示文字列だけ整える
            else:
                self.show_page(n)
        self.canvas.focus_set()

    # ------------------------------------------------------------- 表示方法
    def _on_layout_selected(self, _e=None):
        label = self.layout_combo.get()
        for mode, text in LAYOUT_LABELS.items():
            if text == label:
                self.set_view_mode(mode)
                break

    def _on_cover_toggle(self):
        self.set_cover_alone(self.cover_var.get())

    def _on_binding_selected(self, _e=None):
        label = self.binding_combo.get()
        for b, text in BINDING_LABELS.items():
            if text == label:
                self.set_binding(b)
                break

    def set_binding(self, binding):
        self.binding = binding
        self._sync_view_widgets()
        if self.doc and self.view_mode == "spread":
            self.show_page(self.page_no, None)
        self.canvas.focus_set()
        self.schedule_save()

    def set_view_mode(self, mode):
        self.view_mode = mode
        self._sync_view_widgets()
        if self.fullscreen:
            self._fs_fit_pending = True    # 表示方法の切替時にも全体が収まるよう再調整
        if self.doc:
            self.show_page(self.page_no)
        self.canvas.focus_set()
        self.schedule_save()

    def set_cover_alone(self, flag):
        self.cover_alone = bool(flag)
        self._sync_view_widgets()
        if self.fullscreen and self.view_mode == "spread":
            self._fs_fit_pending = True
        if self.doc and self.view_mode == "spread":
            self.show_page(self.page_no)
        self.canvas.focus_set()
        self.schedule_save()

    # ------------------------------------------------------------- 描画
    def compose_view(self, z, bg):
        """表示中のページ(群)を倍率 z で描画して1枚の画像にする"""
        parts = []
        for pno, xo, yo, _, _ in self.view_layout:
            pix = self.doc[pno].get_pixmap(matrix=fitz.Matrix(z, z), alpha=False)
            img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            parts.append((img, round(xo * z), round(yo * z)))
        if len(parts) == 1:
            return parts[0][0]
        w = max(x + im.width for im, x, _ in parts)
        h = max(y + im.height for im, _, y in parts)
        out = Image.new("RGB", (w, h), bg)
        for im, x, y in parts:
            out.paste(im, (x, y))
        return out

    def render(self):
        img = self.compose_view(self.zoom, BG_RGB)
        self.photo = ImageTk.PhotoImage(img)
        if self.img_id is None:
            self.img_id = self.canvas.create_image(0, 0, image=self.photo, anchor="nw")
        else:
            self.canvas.itemconfig(self.img_id, image=self.photo)
        self.zoom_label.config(text=f"{round(self.zoom / DPI_SCALE * 100)}%")
        self.relayout()

    def relayout(self):
        if self.photo is None:
            return
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        iw, ih = self.photo.width(), self.photo.height()
        self.W = max(cw, iw + 2 * PAD)
        self.H = max(ch, ih + 2 * PAD)
        self.ox = (self.W - iw) // 2
        self.oy = (self.H - ih) // 2
        self.canvas.coords(self.img_id, self.ox, self.oy)
        self.canvas.config(scrollregion=(0, 0, self.W, self.H))
        self.draw_hits()
        self.draw_sel()

    def on_canvas_configure(self, e):
        self.relayout()
        if self.fullscreen and self._fs_fit_pending:
            self._schedule_fs_fit()
        elif self.fit_mode and self.view_pages and e.width != self._last_w:
            self._schedule_refit()
        self._last_w = e.width

    def _schedule_refit(self):
        if self._fit_job:
            self.root.after_cancel(self._fit_job)
        self._fit_job = self.root.after(120, self.refit)

    def refit(self):
        self._fit_job = None
        if not (self.fit_mode and self.view_pages):
            return
        z = self._fit_zoom()
        if abs(z - self.zoom) > 1e-3:
            lo, _ = self.canvas.yview()
            self.zoom = z
            self.render()
            self.canvas.yview_moveto(lo)

    def _draw_rects(self, tag, items):
        c = self.canvas
        c.delete(tag)
        z = self.zoom
        cache = {}
        for r, color in items:
            w = max(1, round((r[2] - r[0]) * z))
            h = max(1, round((r[3] - r[1]) * z))
            im = cache.get((w, h, color))
            if im is None:
                im = cache[(w, h, color)] = ImageTk.PhotoImage(Image.new("RGBA", (w, h), color))
            c.create_image(self.ox + r[0] * z, self.oy + r[1] * z, image=im, anchor="nw", tags=tag)
        self._imgs[tag] = list(cache.values())  # 参照を保持

    def draw_hits(self):
        items = []
        if self.view_pages and self.query:
            for pno, xo, yo, _, _ in self.view_layout:
                for k, r in enumerate(self.get_hits(pno)):
                    color = CUR_COLOR if self.cur_hit == (pno, k) else HIT_COLOR
                    items.append(((r[0] + xo, r[1] + yo, r[2] + xo, r[3] + yo), color))
        self._draw_rects("hit", items)
        self.canvas.tag_raise("sel")

    def sel_rects(self):
        if not self.sel:
            return []
        a, b = self.sel
        per_line = {}
        for i in range(a, b + 1):
            _, r, lid = self.chars[i]
            q = per_line.get(lid)
            per_line[lid] = r if q is None else (min(q[0], r[0]), min(q[1], r[1]),
                                                  max(q[2], r[2]), max(q[3], r[3]))
        return list(per_line.values())

    def draw_sel(self):
        self._draw_rects("sel", [(r, SEL_COLOR) for r in self.sel_rects()])

    # ------------------------------------------------------------- 拡大縮小
    def _fit_zoom(self):
        cw = max(self.canvas.winfo_width(), 200)
        return max(ZOOM_MIN, min(ZOOM_MAX, cw / max(self.view_w, 1.0) * FIT_EPS))

    def zoom_by(self, f, anchor=None):
        self.set_zoom(self.zoom * f, anchor)

    def zoom_100(self):
        self.set_zoom(DPI_SCALE)

    def set_zoom(self, z, anchor=None):
        self.fit_mode = False
        self._fs_fit_pending = False
        self.schedule_save()
        if not self.view_pages:
            self.zoom = max(ZOOM_MIN, min(ZOOM_MAX, z))
            return
        z = max(ZOOM_MIN, min(ZOOM_MAX, z))
        if abs(z - self.zoom) < 1e-9:
            return
        c = self.canvas
        ax, ay = anchor if anchor else (c.winfo_width() / 2, c.winfo_height() / 2)
        px = (c.canvasx(ax) - self.ox) / self.zoom   # アンカー位置にある座標(pt)
        py = (c.canvasy(ay) - self.oy) / self.zoom
        self.zoom = z
        self.render()
        c.xview_moveto(max(0, self.ox + px * z - ax) / self.W)
        c.yview_moveto(max(0, self.oy + py * z - ay) / self.H)

    def fit_width(self):
        self.fit_mode = True
        self._fs_fit_pending = False
        if self.view_pages:
            self.zoom = self._fit_zoom()
            self.render()
            self.canvas.xview_moveto(0)
        self.schedule_save()

    # ------------------------------------------------------------- スクロール
    def on_wheel(self, e):
        if not self.view_pages:
            return
        if e.num == 4:
            d = 1
        elif e.num == 5:
            d = -1
        else:
            d = 1 if e.delta > 0 else -1
        if e.state & 0x4 or (sys.platform == "darwin" and e.state & 0x8):  # Ctrl / Cmd
            self.zoom_by(1.1 ** d, (e.x, e.y))
        elif e.state & 0x1:                                              # Shift
            self.canvas.xview_scroll(-d * 3, "units")
        else:
            self.scroll_or_flip(d)

    def scroll_or_flip(self, d, units=3):
        """d>0: 上へ, d<0: 下へ。端でさらにスクロールしたら前後のページへ移動"""
        if not self.view_pages:
            return
        lo, hi = self.canvas.yview()
        now = time.monotonic()
        if d < 0 and hi >= 0.999:
            if now - self.last_flip > 0.4 and self.view_pages[-1] < len(self.doc) - 1:
                self.last_flip = now
                self.next_view()
        elif d > 0 and lo <= 0.001:
            if now - self.last_flip > 0.4 and self.page_no > 0:
                self.last_flip = now
                self.prev_view("bottom")
        else:
            self.canvas.yview_scroll(-d * units, "units")

    def key_horizontal(self, d):
        lo, hi = self.canvas.xview()
        if lo <= 0 and hi >= 1:
            nav = -d if (self.view_mode == "spread" and self.binding == "right") else d
            self.next_view() if nav > 0 else self.prev_view()
        else:
            self.canvas.xview_scroll(d * 2, "units")

    # ------------------------------------------------------------- 座標/ヒットテスト
    def to_page(self, e):
        return ((self.canvas.canvasx(e.x) - self.ox) / self.zoom,
                (self.canvas.canvasy(e.y) - self.oy) / self.zoom)

    def on_text(self, px, py, m=2.0):
        for x0, y0, x1, y1 in self.lines:
            if x0 - m <= px <= x1 + m and y0 - m <= py <= y1 + m:
                return True
        return False

    def nearest_char(self, px, py):
        best, bd = 0, float("inf")
        for i, (_, r, _) in enumerate(self.chars):
            dx = max(r[0] - px, 0, px - r[2])
            dy = max(r[1] - py, 0, py - r[3])
            d = dx * dx + dy * dy
            if d < bd:
                best, bd = i, d
                if d == 0:
                    break
        return best

    def word_range(self, i):
        ch = self.chars[i][0]
        if ch.isspace():
            return (i, i)
        k, lid = char_kind(ch), self.chars[i][2]
        a = b = i
        while a > 0 and self.chars[a - 1][2] == lid and char_kind(self.chars[a - 1][0]) == k:
            a -= 1
        while b + 1 < len(self.chars) and self.chars[b + 1][2] == lid and char_kind(self.chars[b + 1][0]) == k:
            b += 1
        return (a, b)

    def line_range(self, i):
        lid = self.chars[i][2]
        a = b = i
        while a > 0 and self.chars[a - 1][2] == lid:
            a -= 1
        while b + 1 < len(self.chars) and self.chars[b + 1][2] == lid:
            b += 1
        return (a, b)

    # ------------------------------------------------------------- マウス操作
    def on_press(self, e, count=1):
        self.canvas.focus_set()
        if not self.view_pages:
            return
        px, py = self.to_page(e)
        old = self.sel
        if self.chars and self.on_text(px, py):
            i = self.nearest_char(px, py)
            self.anchor = i
            self.drag_mode = "select"
            if count == 2:
                self.sel = self.word_range(i)
            elif count >= 3:
                self.sel = self.line_range(i)
            else:
                self.sel = None
        else:
            self.sel = None
            self.drag_mode = "pan"
            self.canvas.scan_mark(e.x, e.y)
            self._cursor = "fleur"
            self.canvas.config(cursor="fleur")
        if self.sel != old:
            self.draw_sel()

    def on_drag(self, e):
        if self.drag_mode == "pan":
            self.canvas.scan_dragto(e.x, e.y, gain=1)
        elif self.drag_mode == "select":
            c = self.canvas
            if e.y < 0:
                c.yview_scroll(-1, "units")
            elif e.y > c.winfo_height():
                c.yview_scroll(1, "units")
            if e.x < 0:
                c.xview_scroll(-1, "units")
            elif e.x > c.winfo_width():
                c.xview_scroll(1, "units")
            px, py = self.to_page(e)
            i = self.nearest_char(px, py)
            if i == self.anchor and self.sel is None:
                return
            new = (min(self.anchor, i), max(self.anchor, i))
            if new != self.sel:
                self.sel = new
                self.draw_sel()

    def on_release(self, e):
        self.drag_mode = None
        self._cursor = None
        self.on_motion(e)

    def on_motion(self, e):
        if self.drag_mode or not self.view_pages:
            return
        px, py = self.to_page(e)
        want = "xterm" if self.on_text(px, py) else ""
        if want != self._cursor:
            self._cursor = want
            self.canvas.config(cursor=want)

    # ------------------------------------------------------------- コピー
    def selected_text(self):
        if not self.sel:
            return ""
        a, b = self.sel
        out, prev = [], None
        for ch, _, lid in self.chars[a:b + 1]:
            if prev is not None and lid != prev:
                out.append("\n")
            out.append(ch)
            prev = lid
        return "".join(out)

    def copy_selection(self, _e=None):
        text = self.selected_text()
        if text:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self.root.update()
            self.toast(f"{len(text)} 文字をコピーしました")
        return "break"

    def select_all(self, _e=None):
        if self.chars:
            self.sel = (0, len(self.chars) - 1)
            self.draw_sel()
        return "break"

    # ------------------------------------------------------------- 印刷
    def print_document(self, _e=None):
        """印刷ダイアログを表示して印刷する"""
        if not self.doc:
            return "break"
        try:
            if sys.platform == "win32":
                self._print_windows()
            else:
                self._print_cups()
        except Exception as ex:
            self.root.config(cursor="")
            messagebox.showerror("印刷エラー", f"印刷できませんでした:\n{ex}")
        return "break"

    def _print_windows(self):
        from PIL import ImageWin
        total = len(self.doc)
        hwnd = _user32.GetParent(self.root.winfo_id()) or self.root.winfo_id()
        res = win_print_dialog(hwnd, 1, total, self.view_pages[0] + 1, self.view_pages[-1] + 1)
        if res is None:
            return
        hdc, first, last = res
        pages = list(range(first - 1, min(last, total)))
        info = _DOCINFOW()
        info.cbSize = ctypes.sizeof(info)
        info.lpszDocName = Path(self.path).name if self.path else APP_TITLE
        self.root.config(cursor="watch")
        try:
            if _gdi32.StartDocW(hdc, ctypes.byref(info)) <= 0:
                raise OSError("印刷ジョブを開始できません")
            try:
                for k, pno in enumerate(pages, 1):
                    self.toast(f"印刷中... {k}/{len(pages)}", 60000)
                    self.root.update_idletasks()
                    if _gdi32.StartPage(hdc) <= 0:
                        raise OSError("ページを開始できません")
                    hres = _gdi32.GetDeviceCaps(hdc, HORZRES)   # 印刷可能領域(デバイスpx)
                    vres = _gdi32.GetDeviceCaps(hdc, VERTRES)
                    w, h = self.doc[pno].rect.width, self.doc[pno].rect.height
                    rotate = (w > h) != (hres > vres)           # 用紙の向きに合わせて回転
                    pw, ph = (h, w) if rotate else (w, h)
                    scale = min(hres / pw, vres / ph)           # デバイスpx / pt
                    rs = min(scale, PRINT_MAX_DPI / 72)
                    pix = self.doc[pno].get_pixmap(matrix=fitz.Matrix(rs, rs), alpha=False)
                    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                    if rotate:
                        img = img.rotate(90, expand=True)
                    dw, dh = int(pw * scale), int(ph * scale)
                    x, y = (hres - dw) // 2, (vres - dh) // 2   # 印刷可能領域の中央に配置
                    ImageWin.Dib(img).draw(hdc, (x, y, x + dw, y + dh))
                    _gdi32.EndPage(hdc)
            except Exception:
                _gdi32.AbortDoc(hdc)
                raise
            _gdi32.EndDoc(hdc)
        finally:
            _gdi32.DeleteDC(hdc)
            self.root.config(cursor="")
        self.toast(f"{len(pages)} ページを印刷に送りました", 4000)

    def _print_cups(self):
        """macOS / Linux: 簡易の印刷ダイアログ + lp コマンド (CUPS)"""
        if not shutil.which("lp"):
            messagebox.showerror("印刷", "lp コマンド(CUPS)が見つからないため印刷できません。")
            return
        printers, default = [], ""
        try:
            out = subprocess.run(["lpstat", "-e"], capture_output=True, text=True, timeout=10).stdout
            printers = [ln.strip() for ln in out.splitlines() if ln.strip()]
            out = subprocess.run(["lpstat", "-d"], capture_output=True, text=True, timeout=10).stdout
            default = out.rsplit(":", 1)[-1].strip() if ":" in out else ""
        except (OSError, subprocess.SubprocessError):
            pass

        dlg = tk.Toplevel(self.root)
        dlg.title("印刷")
        dlg.transient(self.root)
        dlg.resizable(False, False)
        frm = ttk.Frame(dlg, padding=12)
        frm.pack()
        ttk.Label(frm, text="プリンタ:").grid(row=0, column=0, sticky="w", pady=3)
        printer_var = tk.StringVar(value=default if default in printers else (printers[0] if printers else ""))
        ttk.Combobox(frm, textvariable=printer_var, values=printers, width=28).grid(row=0, column=1, columnspan=2, pady=3)
        ttk.Label(frm, text="部数:").grid(row=1, column=0, sticky="w", pady=3)
        copies_var = tk.StringVar(value="1")
        ttk.Spinbox(frm, from_=1, to=99, textvariable=copies_var, width=5).grid(row=1, column=1, sticky="w", pady=3)
        range_mode = tk.StringVar(value="all")
        ttk.Radiobutton(frm, text="すべてのページ", variable=range_mode, value="all").grid(row=2, column=0, columnspan=3, sticky="w")
        ttk.Radiobutton(frm, text="ページ指定 (例: 1-3,5):", variable=range_mode, value="range").grid(row=3, column=0, columnspan=2, sticky="w")
        range_var = tk.StringVar(value=str(self.page_no + 1))
        range_entry = ttk.Entry(frm, textvariable=range_var, width=12)
        range_entry.grid(row=3, column=2, sticky="w")
        range_entry.bind("<FocusIn>", lambda e: range_mode.set("range"))
        result = {}

        def ok():
            copies = copies_var.get().strip()
            rng = range_var.get().replace(" ", "")
            if not printer_var.get():
                messagebox.showerror("印刷", "プリンタを選択してください。", parent=dlg)
            elif not copies.isdigit() or int(copies) < 1:
                messagebox.showerror("印刷", "部数が正しくありません。", parent=dlg)
            elif range_mode.get() == "range" and not re.fullmatch(r"\d+(-\d+)?(,\d+(-\d+)?)*", rng):
                messagebox.showerror("印刷", "ページ指定が正しくありません。", parent=dlg)
            else:
                result.update(printer=printer_var.get(), copies=int(copies),
                              range=rng if range_mode.get() == "range" else "")
                dlg.destroy()

        btns = ttk.Frame(frm)
        btns.grid(row=4, column=0, columnspan=3, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="印刷", command=ok).pack(side="left", padx=4)
        ttk.Button(btns, text="キャンセル", command=dlg.destroy).pack(side="left")
        dlg.bind("<Return>", lambda e: ok())
        dlg.bind("<Escape>", lambda e: dlg.destroy())
        dlg.grab_set()
        self.root.wait_window(dlg)
        if not result:
            return

        path, tmp = self.path, None
        if self.doc.is_encrypted:                     # パスワード付きPDFは復号したコピーを印刷
            fd, tmp = tempfile.mkstemp(suffix=".pdf")
            os.close(fd)
            self.doc.save(tmp, encryption=fitz.PDF_ENCRYPT_NONE)
            path = tmp
        cmd = ["lp", "-d", result["printer"], "-n", str(result["copies"])]
        if result["range"]:
            cmd += ["-P", result["range"]]
        cmd.append(path)
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        finally:
            if tmp:
                try:
                    os.remove(tmp)
                except OSError:
                    pass
        if r.returncode != 0:
            raise RuntimeError(r.stderr.strip() or "lp がエラーを返しました")
        self.toast("印刷に送りました", 4000)

    # ------------------------------------------------------------- 画像として保存
    def save_capture(self, _e=None):
        """表示中のページ(見開きなら2ページ分)を PNG にして PDF と同じフォルダへ保存"""
        if not (self.doc and self.view_pages and self.path):
            return "break"
        img = self.compose_view(CAPTURE_DPI / 72, (255, 255, 255))
        width = max(3, len(str(len(self.doc))))
        nums = [f"{p + 1:0{width}d}" for p in self.view_pages]
        label = nums[0] if len(nums) == 1 else f"{nums[0]}-{nums[-1]}"
        pdf = Path(self.path).resolve()
        out = pdf.parent / f"{pdf.stem}_p{label}.png"
        k = 2
        while out.exists():                       # 既存ファイルは上書きしない
            out = pdf.parent / f"{pdf.stem}_p{label}_{k}.png"
            k += 1
        try:
            img.save(out, "PNG")
        except OSError as ex:
            messagebox.showerror("保存エラー", f"画像を保存できませんでした:\n{ex}")
            return "break"
        self.toast(f"保存しました: {out.name}", 4000)
        return "break"

    # ------------------------------------------------------------- 検索
    def open_search(self, _e=None):
        if not self.search_visible:
            self.search_bar.grid()
            self.search_visible = True
            self._update_top()
        text = " ".join(self.selected_text().split())[:100]
        if text:
            self.search_var.set(text)
        self.search_entry.focus_set()
        self.search_entry.select_range(0, "end")
        return "break"

    def close_search(self):
        if not self.search_visible:
            return
        self.search_bar.grid_remove()
        self.search_visible = False
        self._update_top()
        self.query = None
        self.cur_hit = None
        self.hit_cache.clear()
        self.draw_hits()
        self.canvas.focus_set()

    def _on_search_change(self, *_):
        self.query = self.search_var.get() or None
        self.hit_cache.clear()
        self.cur_hit = None
        if self.view_pages:
            self.draw_hits()
        self.update_search_info()

    def get_hits(self, pno):
        if pno not in self.hit_cache:
            rects = self.doc[pno].search_for(self.query) if self.query else []
            self.hit_cache[pno] = [(r.x0, r.y0, r.x1, r.y1) for r in rects]
        return self.hit_cache[pno]

    def update_search_info(self):
        if not self.query or not self.view_pages:
            self.search_info.config(text="")
            return
        total, cur = 0, None
        for pno in self.view_pages:
            if self.cur_hit and self.cur_hit[0] == pno:
                cur = total + self.cur_hit[1] + 1
            total += len(self.get_hits(pno))
        self.search_info.config(text=f"表示中 {cur}/{total} 件" if cur else f"表示中 {total} 件")

    def find(self, d=1):
        """d=1: 次, d=-1: 前 (全ページを巡回して検索)"""
        if not self.doc:
            return
        if not self.search_visible:
            self.open_search()
            return
        if not self.query:
            return
        total = len(self.doc)
        if self.cur_hit is None:
            p = self.page_no if d > 0 else self.view_pages[-1]
            i = -1 if d > 0 else len(self.get_hits(p))
        else:
            p, i = self.cur_hit
        self.root.config(cursor="watch")
        self.root.update_idletasks()
        try:
            for _ in range(total + 1):
                hits = self.get_hits(p)
                j = i + d
                if 0 <= j < len(hits):
                    self.cur_hit = (p, j)
                    self.goto_hit()
                    return
                p = (p + d) % total
                i = -1 if d > 0 else len(self.get_hits(p))
            self.search_info.config(text="見つかりませんでした")
        finally:
            self.root.config(cursor="")

    def goto_hit(self):
        p, j = self.cur_hit
        if p not in self.view_pages:
            self.show_page(p, None)
        else:
            self.draw_hits()
        xo, yo = next((x, y) for pno, x, y, _, _ in self.view_layout if pno == p)
        r = self.get_hits(p)[j]
        z = self.zoom
        cx = self.ox + ((r[0] + r[2]) / 2 + xo) * z
        cy = self.oy + ((r[1] + r[3]) / 2 + yo) * z
        self.canvas.xview_moveto(max(0, cx - self.canvas.winfo_width() / 2) / self.W)
        self.canvas.yview_moveto(max(0, cy - self.canvas.winfo_height() / 2) / self.H)
        self.update_search_info()


def main():
    try:  # Windows: 高DPIでぼやけないように
        from ctypes import windll
        windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    try:  # Windows: python.exe ではなく、このアプリとしてタスクバーのアイコンを扱わせる
        from ctypes import windll
        windll.shell32.SetCurrentProcessExplicitAppUserModelID("SimplePDFViewer.App")
    except Exception:
        pass
    root = tk.Tk()
    PdfViewer(root, sys.argv[1] if len(sys.argv) > 1 else None)
    root.mainloop()


if __name__ == "__main__":
    main()
