"""Neon: a tiny cyberpunk fox that wanders around your desktop.

Run with ``python neon_pet.py``. On 4K displays Neon scales up automatically;

set ``NEON_SCALE=2`` to override the size. Uses only Python's standard library.

At startup Neon applies a newer, syntax-checked ``neon.zip`` without prompting.

It checks while running, waits for the new window to report healthy, and restores

the previous package if startup fails. Increase ``APP_VERSION`` for future bundles.

Click Neon to pet, drag to pick it up, or use the little toolbar to feed and play.

"""

import ast

import csv

import base64

import ctypes

import ctypes.wintypes

import json

import math

import os

import random

import socket

import ssl

import stat

import shutil

import subprocess

import sys

import tempfile

import threading

import zipfile

import time

import tkinter as tk

try:

    from PIL import Image, ImageTk

except ImportError:

    Image = ImageTk = None

from tkinter import filedialog, messagebox, simpledialog

from pathlib import Path, PurePosixPath

KEY = "#010203"                 # transparent window color on Windows

BG = "#0c1021"

INK = "#18223d"

CYAN = "#6cc4ff"

PINK = "#f3a6d8"

PURPLE = "#47a6f0"

WHITE = "#eaf6ff"

MUTED = "#a0accb"

STATE_PATH = Path.home() / ".neon_pet_state.json"

CODE_BACKUP_PATH = Path(__file__).resolve().with_name(".neon_pet.py.last_good")

AUTO_FEED_INTERVAL_MS = 15 * 60 * 1000

APP_VERSION = 51

TICK_MS = 50

GLOW_PALETTES = {
    "Cyan": "#47a6f0",
    "Magenta": "#ff4fd8",
    "Violet": "#9b67ff",
    "Amber": "#ffd34d",
    "Mint": "#67f7c1",
}

PERSONALITIES = {

    "Chill": {"hop_wait": (220, 340), "hop_seconds": 1.25,

              "surface_speed": 5.0, "crawl_delay": 1000,

              "cursor_cooldown": 800, "cursor_radius": 100},

    "Curious": {"hop_wait": (100, 180), "hop_seconds": 1.0,

                "surface_speed": 8.0, "crawl_delay": 600,

                "cursor_cooldown": 400, "cursor_radius": 130},

    "Hyper": {"hop_wait": (55, 95), "hop_seconds": 0.7,

              "surface_speed": 11.0, "crawl_delay": 320,

              "cursor_cooldown": 200, "cursor_radius": 170},

}

class Neon:

    def __init__(self, root):

        self.root = root

        self.root.title("Neon.exe")

        self.root.overrideredirect(True)

        self.root.attributes("-topmost", True)

        try:

            self.root.configure(bg=KEY)

            self.root.wm_attributes("-transparentcolor", KEY)

        except tk.TclError:

            self.root.configure(bg=BG)

        self.screen_w = root.winfo_screenwidth()

        self.screen_h = root.winfo_screenheight()

        default_scale = 0.75 if self.screen_w >= 3200 or self.screen_h >= 1800 else 0.5

        try:

            requested_scale = float(os.environ.get("NEON_SCALE", default_scale))

        except ValueError:

            requested_scale = default_scale

        self.scale = min(2.5, max(0.25, requested_scale))

        try:

            current_tk_scale = float(root.tk.call("tk", "scaling"))

            root.tk.call("tk", "scaling", current_tk_scale * self.scale)

            self.menu_font_base_size = 10

            for font_name in ("TkDefaultFont", "TkTextFont", "TkFixedFont", "TkMenuFont",

                              "TkHeadingFont", "TkCaptionFont", "TkSmallCaptionFont",

                              "TkTooltipFont", "TkIconFont"):

                try:

                    current_size = int(root.tk.call("font", "actual", font_name, "-size"))

                    if font_name == "TkMenuFont":

                        self.menu_font_base_size = current_size

                    increment = 10 if font_name == "TkMenuFont" else 5

                    root.tk.call("font", "configure", font_name, "-size", current_size + increment)

                except (tk.TclError, ValueError):

                    continue

        except (tk.TclError, ValueError):

            pass

        self.width, self.height = round(300 * self.scale), round(306 * self.scale)

        self.icon_targets = self.load_desktop_icons()

        self.icon_target_index = 0

        self.toolbar_position = None

        self.toolbar_drag_origin = None

        self.personality = "Curious"

        self.movement_speed = 1.0

        self.voice_enabled = True

        self.voice_lock = threading.Lock()

        self.next_auto_speech_frame = 0

        self.patrol_route = list(range(len(self.icon_targets)))

        self.route_cursor = 0

        self.route_presets = {

            "All apps": list(range(len(self.icon_targets))),

            "Favorites": list(range(min(5, len(self.icon_targets)))),

            "Custom": list(self.patrol_route),

        }

        self.active_route_preset = "Custom"

        self.next_hop_frame = 80

        self.hop_start = None

        self.hop_target = None

        self.hop_elapsed = 0.0

        self.hop_duration = 1.0

        self.desktop_visible = True

        self.window_hidden = False

        self.radar_press = False

        self.ceiling_pending = False

        self.ceiling_until = 0

        self.patrol_paused = False

        self.zoomies_until = 0

        self.wave_until = 0

        self.next_cursor_wave = 0

        self.home_perch = None

        self.manual_destination = None

        self.teleport_phase = None

        self.teleport_target = None

        self.teleport_started_frame = 0

        self.teleport_phase_until = 0

        self.teleport_from = None

        self.teleport_echo_cache = {}

        self.affection_until = 0

        self.landing_frame = -1000

        self.route_history = []

        self.patrol_log = []

        self.wall_side = "right"

        self.wall_direction = 1

        self.next_crawl_frame = PERSONALITIES[self.personality]["crawl_delay"]

        self.canvas = tk.Canvas(root, width=self.width, height=self.height,

                                bg=KEY, highlightthickness=0)

        self.canvas.pack()

        self.sprite_pose_cache = {}

        self.pet_animations = self.load_animations()

        self.x = max(0, (self.screen_w - self.width) // 2)

        self.y = self.screen_h - self.height - 12

        self.target_x = self.x

        self.facing = 1

        self.frame = 0

        self.mode = "idle"

        self.focus_end = None

        self.game_window = None

        self.focus_end = None

        self.game_window = None

        self.sleeping = False

        self.dragging = False

        self.vy = 0

        self.message = "hey, I'm Neon!"

        self.message_ticks = 70

        self.xp = 0

        self.hunger, self.mood, self.energy = 82.0, 85.0, 90.0

        self.best = 0

        self.auto_feed = True

        self.auto_feed_interval_minutes = AUTO_FEED_INTERVAL_MS // 60_000

        self.menu_font_points = 10

        self.glow_theme = "Cyan"

        self.voice_rate = 1

        self.voice_volume = 90

        self.voice_name = ""

        self.auto_feed_job = None

        self.focus_end = None

        self.game_window = None

        self.load_state()

        self.auto_feed_var = tk.BooleanVar(master=root, value=self.auto_feed)

        self.voice_var = tk.BooleanVar(master=root, value=self.voice_enabled)

        self.create_fixed_toolbar()

        self.draw()

        self.bind_mouse()

        self.root.protocol("WM_DELETE_WINDOW", self.quit)

        self.root.bind("<Escape>", lambda _event: self.quit())

        self.move_window()

        self.root.after(TICK_MS, self.tick)

        self.root.after(1400, lambda: self.say("Hi, I'm Neon. Ready to roam?"))

        if self.auto_feed:

            self.auto_feed_job = self.root.after(self.auto_feed_interval_minutes * 60_000, self.auto_feed_tick)

        self.root.after(5 * 60 * 1000, self.check_for_updates)

        self.root.after(5 * 60 * 1000, self.auto_rescan_desktop_icons)

    @property

    def level(self):

        return 1 + int(math.sqrt(self.xp / 10))

    def load_state(self):

        backup = STATE_PATH.with_suffix(".bak")

        loaded_from_backup = False

        data = None

        for candidate in (STATE_PATH, backup):

            try:

                parsed = json.loads(candidate.read_text(encoding="utf-8"))

                if isinstance(parsed, dict):

                    data = parsed

                    loaded_from_backup = candidate == backup

                    break

            except (OSError, ValueError, TypeError):

                continue

        if data is None:

            return

        for key in ("hunger", "mood", "energy"):

            value = data.get(key)

            if isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value):

                setattr(self, key, min(100, max(0, float(value))))

        for key in ("xp", "best"):

            value = data.get(key)

            if isinstance(value, int) and not isinstance(value, bool) and value >= 0:

                setattr(self, key, value)

        saved_toolbar = data.get("toolbar_position")

        if (isinstance(saved_toolbar, list) and len(saved_toolbar) == 2

                and all(isinstance(v, (int, float)) and not isinstance(v, bool)

                        and math.isfinite(v) for v in saved_toolbar)):

            self.toolbar_position = (int(saved_toolbar[0]), int(saved_toolbar[1]))

        saved_personality = data.get("personality")

        if isinstance(saved_personality, str) and saved_personality in PERSONALITIES:

            self.personality = saved_personality

        if isinstance(data.get("auto_feed"), bool):

            self.auto_feed = data["auto_feed"]

        saved_speed = data.get("movement_speed")
        if (isinstance(saved_speed, (int, float)) and not isinstance(saved_speed, bool)
                and math.isfinite(saved_speed) and 0.5 <= saved_speed <= 2.0):
            self.movement_speed = float(saved_speed)

        saved_glow_theme = data.get("glow_theme")
        if isinstance(saved_glow_theme, str) and saved_glow_theme in GLOW_PALETTES:
            self.glow_theme = saved_glow_theme

        saved_feed_interval = data.get("auto_feed_interval_minutes")
        if (isinstance(saved_feed_interval, int) and not isinstance(saved_feed_interval, bool)
                and 5 <= saved_feed_interval <= 60):
            self.auto_feed_interval_minutes = saved_feed_interval

        if isinstance(data.get("voice_enabled"), bool):

            self.voice_enabled = data["voice_enabled"]

        saved_voice_rate = data.get("voice_rate")

        if (isinstance(saved_voice_rate, int) and not isinstance(saved_voice_rate, bool)

                and -10 <= saved_voice_rate <= 10):

            self.voice_rate = saved_voice_rate

        saved_voice_volume = data.get("voice_volume")

        if (isinstance(saved_voice_volume, int) and not isinstance(saved_voice_volume, bool)

                and 0 <= saved_voice_volume <= 100):

            self.voice_volume = saved_voice_volume

        saved_voice_name = data.get("voice_name")

        if isinstance(saved_voice_name, str) and len(saved_voice_name) <= 128:

            self.voice_name = saved_voice_name

        saved_menu_font_points = data.get("menu_font_points")

        if (isinstance(saved_menu_font_points, int) and not isinstance(saved_menu_font_points, bool)

                and 0 <= saved_menu_font_points <= 25):

            self.menu_font_points = saved_menu_font_points

        try:

            self.root.tk.call("font", "configure", "TkMenuFont", "-size",

                              self.menu_font_base_size + self.menu_font_points)

        except tk.TclError:

            pass

        home = data.get("home_perch")

        if (isinstance(home, list) and len(home) == 2

                and all(isinstance(value, (int, float)) and not isinstance(value, bool)

                        and math.isfinite(value) for value in home)):

            self.home_perch = (

                min(max(0, float(home[0])), self.screen_w - self.width),

                min(max(0, float(home[1])), self.screen_h - self.height))

        icon_keys = self.desktop_icon_keys()

        key_to_index = {key: index for index, key in enumerate(icon_keys)}

        def decode_route(values):

            if not isinstance(values, list):

                return []

            result = []

            for value in values:

                if isinstance(value, str):

                    index = key_to_index.get(value)

                elif isinstance(value, int) and not isinstance(value, bool):

                    index = value

                else:

                    index = None

                if index is not None and 0 <= index < len(self.icon_targets) and index not in result:

                    result.append(index)

            return result

        self.next_crawl_frame = self.frame + PERSONALITIES[self.personality]["crawl_delay"]

        saved_route = decode_route(data.get("patrol_route"))

        saved_presets = data.get("route_presets")

        if isinstance(saved_presets, dict):

            restored = {}

            for name, values in list(saved_presets.items())[:24]:

                if isinstance(name, str) and name.strip():

                    restored[name[:24]] = decode_route(values)

            if restored:

                self.route_presets.update(restored)

        if saved_route:

            self.patrol_route = saved_route

            self.route_presets["Custom"] = list(saved_route)

        active = data.get("active_route_preset")

        if isinstance(active, str) and active in self.route_presets:

            self.active_route_preset = active

            if self.route_presets[active]:

                self.patrol_route = list(self.route_presets[active])

        else:

            self.active_route_preset = "Custom"

        self.icon_scan_busy = False

        saved_log = data.get("patrol_log", [])

        if isinstance(saved_log, list):

            for entry in saved_log[-30:]:

                if not isinstance(entry, dict):

                    continue

                name, stamp, x, y = (entry.get("name"), entry.get("time"),

                                     entry.get("x"), entry.get("y"))

                if (isinstance(name, str) and isinstance(stamp, str)

                        and isinstance(x, (int, float)) and math.isfinite(x)

                        and isinstance(y, (int, float)) and math.isfinite(y)):

                    self.patrol_log.append({"name": name[:32], "time": stamp[:24],

                                            "x": int(x), "y": int(y)})

        saved_at = data.get("saved")

        if isinstance(saved_at, (int, float)) and math.isfinite(saved_at):

            elapsed = min(max(0, time.time() - saved_at), 6 * 3600)

            self.hunger = max(0, self.hunger - elapsed / 84)

            self.mood = max(0, self.mood - elapsed / 900)

            self.energy = max(0, self.energy - elapsed / 200)

        if loaded_from_backup:

            self.say("save data recovered from backup.")

            try:

                repair = STATE_PATH.with_suffix(".restore.tmp")

                repair.write_text(json.dumps(data), encoding="utf-8")

                repair.replace(STATE_PATH)

            except OSError:

                pass

    def save_state(self):

        data = {key: getattr(self, key) for key in ("hunger", "mood", "energy", "xp", "best")}

        data["auto_feed"] = self.auto_feed
        data["auto_feed_interval_minutes"] = self.auto_feed_interval_minutes
        data["glow_theme"] = self.glow_theme
        data["movement_speed"] = self.movement_speed

        data["voice_enabled"] = self.voice_enabled

        data["menu_font_points"] = self.menu_font_points

        data["voice_rate"] = self.voice_rate

        data["voice_volume"] = self.voice_volume

        data["voice_name"] = self.voice_name

        data["home_perch"] = list(self.home_perch) if self.home_perch is not None else None

        data["patrol_log"] = self.patrol_log[-30:]

        icon_keys = self.desktop_icon_keys()

        data["patrol_route"] = [icon_keys[i] for i in self.patrol_route if 0 <= i < len(icon_keys)]

        data["route_presets"] = {

            name: [icon_keys[i] for i in route if 0 <= i < len(icon_keys)]

            for name, route in self.route_presets.items()

        }

        data["active_route_preset"] = self.active_route_preset

        data["personality"] = self.personality

        data["toolbar_position"] = list(self.toolbar_position) if self.toolbar_position else None

        data["saved"] = time.time()

        try:

            temp = STATE_PATH.with_suffix(".tmp")

            temp.write_text(json.dumps(data), encoding="utf-8")

            try:

                previous = json.loads(STATE_PATH.read_text(encoding="utf-8"))

                if isinstance(previous, dict):

                    backup_temp = STATE_PATH.with_suffix(".bak.tmp")

                    backup_temp.write_text(json.dumps(previous), encoding="utf-8")

                    backup_temp.replace(STATE_PATH.with_suffix(".bak"))

            except (OSError, ValueError, TypeError):

                pass

            temp.replace(STATE_PATH)

        except OSError:

            pass

    def desktop_icon_keys(self, icons=None):

        icons = self.icon_targets if icons is None else icons

        seen = {}

        keys = []

        for _x, _y, label in icons:

            base = label.strip().casefold() or "desktop icon"

            seen[base] = seen.get(base, 0) + 1

            keys.append(f"{base}::{seen[base]}")

        return keys

    def load_desktop_icons(self):

        if os.name != "nt":

            return []

        script = (

            "$ErrorActionPreference='Stop'; Add-Type -AssemblyName UIAutomationClient; "

            "$root=[System.Windows.Automation.AutomationElement]::RootElement; "

            "$condition=New-Object System.Windows.Automation.PropertyCondition("

            "[System.Windows.Automation.AutomationElement]::ClassNameProperty,'SysListView32'); "

            "$list=$root.FindFirst([System.Windows.Automation.TreeScope]::Descendants,$condition); "

            "$positions=@(); if ($null -ne $list) { "

            "$items=$list.FindAll([System.Windows.Automation.TreeScope]::Children,"

            "[System.Windows.Automation.Condition]::TrueCondition); "

            "foreach($item in $items) { $r=$item.Current.BoundingRectangle; "

            "if($r.Width -gt 0 -and $r.Height -gt 0) { "

            "$positions += [pscustomobject]@{x=$r.X;y=$r.Y;width=$r.Width;height=$r.Height;name=$item.Current.Name} } } }; "

            "ConvertTo-Json -InputObject @($positions) -Compress")

        try:

            result = subprocess.run(self.powershell(script), capture_output=True, text=True,

                                    timeout=10, check=True,

                                    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))

            data = json.loads(result.stdout)

            if isinstance(data, dict):

                data = [data]

            targets = []

            for item in data:

                cx = float(item["x"]) + float(item["width"]) / 2

                cy = float(item["y"]) + float(item["height"]) / 2

                if not (0 <= cx < self.screen_w and 0 <= cy < self.screen_h):

                    continue

                x = round(cx - self.width / 2)

                y = round(cy - self.height * 0.32)

                x = min(max(0, x), self.screen_w - self.width)

                y = min(max(0, y), self.screen_h - self.height)

                targets.append((x, y, str(item.get("name", "Desktop icon")).strip()[:24] or "Desktop icon"))

            return targets

        except (OSError, subprocess.SubprocessError, ValueError, KeyError, TypeError):

            return []

    def create_fixed_toolbar(self):

        self.toolbar = tk.Toplevel(self.root)

        self.toolbar.title("Neon // Controls")

        self.toolbar.overrideredirect(True)

        self.toolbar.attributes("-topmost", True)

        self.toolbar.configure(bg="#11182e")

        width, height = 264, 48

        x = max(12, self.screen_w - width - 18)

        y = max(12, self.screen_h - height - 70)

        if self.toolbar_position is not None:

            x, y = self.toolbar_position

        x = min(max(0, x), max(0, self.screen_w - width))

        y = min(max(0, y), max(0, self.screen_h - height))

        self.toolbar_position = (x, y)

        self.toolbar.geometry(f"{width}x{height}+{x}+{y}")

        panel = tk.Frame(self.toolbar, bg="#11182e", highlightthickness=1,

                         highlightbackground="#48557b")

        panel.pack(fill="both", expand=True)

        grip = tk.Label(panel, text="MOVE", bg="#11182e", fg=MUTED,

                        font=("Consolas", 12, "bold"), cursor="fleur", padx=5)

        grip.pack(side="left", fill="y", padx=(3, 1))

        grip.bind("<ButtonPress-1>", self.toolbar_drag_start)

        grip.bind("<B1-Motion>", self.toolbar_drag)

        grip.bind("<ButtonRelease-1>", self.toolbar_drag_end)

        style = {"bg": "#17233c", "relief": "flat", "font": ("Consolas", 14, "bold"),

                 "activebackground": "#273456", "activeforeground": CYAN,

                 "padx": 9, "pady": 5}

        tk.Button(panel, text="+ FEED", command=self.feed, fg=PINK, **style).pack(

            side="left", fill="both", expand=True, padx=(4, 2), pady=4)

        tk.Button(panel, text="* PLAY", command=self.play, fg=PURPLE, **style).pack(

            side="left", fill="both", expand=True, padx=2, pady=4)

        tk.Button(panel, text="... MENU", command=self.popup_from_toolbar, fg=CYAN, **style).pack(

            side="left", fill="both", expand=True, padx=(2, 4), pady=4)

    def toolbar_drag_start(self, event):

        self.toolbar_drag_origin = (event.x_root, event.y_root,

                                   self.toolbar.winfo_x(), self.toolbar.winfo_y())

    def toolbar_drag(self, event):

        if self.toolbar_drag_origin is None:

            return

        start_x, start_y, origin_x, origin_y = self.toolbar_drag_origin

        x = min(max(0, origin_x + event.x_root - start_x), self.screen_w - self.toolbar.winfo_width())

        y = min(max(0, origin_y + event.y_root - start_y), self.screen_h - self.toolbar.winfo_height())

        self.toolbar.geometry(f"+{x}+{y}")

        self.toolbar_position = (x, y)

    def toolbar_drag_end(self, _event):

        self.toolbar_drag_origin = None

        self.toolbar_position = (self.toolbar.winfo_x(), self.toolbar.winfo_y())

        self.save_state()

    def reset_toolbar_position(self):

        width, height = self.toolbar.winfo_width(), self.toolbar.winfo_height()

        x = max(0, self.screen_w - width - 18)

        y = max(0, self.screen_h - height - 70)

        self.toolbar.geometry(f"+{x}+{y}")

        self.toolbar_position = (x, y)

        self.save_state()

    def popup_from_toolbar(self):

        event = type("ToolbarEvent", (), {

            "x_root": self.toolbar.winfo_rootx() + self.toolbar.winfo_width() - 8,

            "y_root": self.toolbar.winfo_rooty() + self.toolbar.winfo_height() - 8,

        })()

        self.popup(event)

    def bind_mouse(self):

        self.canvas.bind("<ButtonPress-1>", self.press)

        self.canvas.bind("<B1-Motion>", self.drag)

        self.canvas.bind("<ButtonRelease-1>", self.release)

        self.canvas.bind("<Button-3>", self.popup)

    def move_window(self):

        self.root.geometry(f"{self.width}x{self.height}+{int(self.x)}+{int(self.y)}")

    def load_animations(self):

        scales = (0.5, 0.75, 1.0, 1.5)

        chosen = min(scales, key=lambda value: abs(value - self.scale))

        scale_tag = str(chosen).replace(".", "_")
        self.animation_scale_tag = scale_tag

        assets = Path(__file__).resolve().parent / "assets"

        animation_sizes = {"idle": 6, "right": 8, "left": 8, "wave": 4, "jump": 5}

        animations = {}

        try:

            for animation, count in animation_sizes.items():

                animations[animation] = [

                    tk.PhotoImage(master=self.root,

                                  file=str(assets / f"codex_{animation}_{scale_tag}_{index}.png"))

                    for index in range(count)

                ]

        except tk.TclError:

            return {}

        if Image is not None and ImageTk is not None:

            try:

                for direction in ("left", "right"):

                    animations[f"ceiling_{direction}"] = [

                        ImageTk.PhotoImage(

                            Image.open(assets / f"codex_{direction}_{scale_tag}_{index}.png")

                            .transpose(Image.Transpose.ROTATE_180), master=self.root)

                        for index in range(animation_sizes[direction])

                    ]

                for pose, rotation in (("wall_down", Image.Transpose.ROTATE_270),

                                       ("wall_up", Image.Transpose.ROTATE_90)):

                    animations[pose] = [

                        ImageTk.PhotoImage(

                            Image.open(assets / f"codex_right_{scale_tag}_{index}.png")

                            .transpose(rotation), master=self.root)

                        for index in range(animation_sizes["right"])

                    ]

            except (OSError, tk.TclError, AttributeError):

                animations.pop("ceiling_left", None)

                animations.pop("ceiling_right", None)

        return animations

    def press(self, event):

        self.radar_press = bool(

            self.icon_targets

            and 92 * self.scale <= event.x <= 208 * self.scale

            and 203 * self.scale <= event.y <= 261 * self.scale)

        self.drag_start = (event.x_root, event.y_root)

        self.drag_origin = (self.x, self.y)

        self.dragging = False

    def drag(self, event):

        dx = event.x_root - self.drag_start[0]

        dy = event.y_root - self.drag_start[1]

        if not self.dragging and abs(dx) + abs(dy) > 5:

            self.dragging = True

            self.sleeping = False

            self.mode = "drag"

            self.say("wheee!")

        if self.dragging:

            self.x = min(max(0, self.drag_origin[0] + dx), self.screen_w - self.width)

            self.y = min(max(0, self.drag_origin[1] + dy), self.screen_h - self.height)

            self.move_window()

    def release(self, event):

        if self.dragging:

            self.dragging = False

            self.mode = "fall"

            self.vy = 0

        else:

            rel_y = self.canvas.winfo_pointery() - self.root.winfo_rooty()

            if self.icon_targets and self.radar_press:

                self.radar_press = False

                map_x = min(205, max(95, event.x / self.scale))

                map_y = min(258, max(206, event.y / self.scale))

                map_w = max(1, self.screen_w - self.width)

                map_h = max(1, self.screen_h - self.height)

                desktop_x = (map_x - 95) / 110 * map_w

                desktop_y = (map_y - 206) / 52 * map_h

                self.icon_target_index = min(

                    range(len(self.icon_targets)),

                    key=lambda index: math.dist((desktop_x, desktop_y),

                                                self.icon_targets[index][:2]))

                self.sleeping = False

                self.next_hop_frame = self.frame

                self.start_icon_hop(target_index=self.icon_target_index)

            elif self.icon_targets:

                self.radar_press = False

                self.pet()

            elif 48 * self.scale <= rel_y <= 184 * self.scale:

                self.pet()

    def popup(self, event):

        menu = tk.Menu(self.root, tearoff=0, bg="#11182e", fg=WHITE,

                       activebackground="#273456", activeforeground=CYAN)

        menu.add_command(label="Feed Neon", command=self.feed)

        menu.add_command(label="Junk Snack… (old temp files)", command=self.feed_on_junk)

        menu.add_command(label="Bit Catcher mini-game", command=self.open_game)

        menu.add_command(label="Play", command=self.play)

        menu.add_command(label="Ceiling crawl now", command=self.begin_ceiling_crawl)

        menu.add_command(label="Return to icon patrol", command=self.return_to_patrol)

        menu.add_command(label="Resume patrol" if self.patrol_paused else "Pause patrol",

                         command=self.toggle_patrol)

        menu.add_command(label="Zoomies! (30 seconds)", command=self.start_zoomies)

        menu.add_command(label="Teleport randomly", command=self.teleport_pet)

        menu.add_command(label="Pin current spot as home", command=self.pin_home_perch)

        menu.add_command(label="Go to saved home", command=self.go_home)

        menu.add_command(label="Edit patrol route", command=self.edit_patrol_route)

        menu.add_command(label="Preview patrol route", command=self.preview_patrol_route)

        menu.add_command(label="Reset dock position", command=self.reset_toolbar_position)

        personality_menu = tk.Menu(menu, tearoff=0, bg="#11182e", fg=WHITE,

                                   activebackground="#273456", activeforeground=CYAN)

        for profile in PERSONALITIES:

            personality_menu.add_command(

                label=(f"✓ {profile}" if profile == self.personality else profile),

                command=lambda name=profile: self.set_personality(name))

        menu.add_cascade(label=f"Personality: {self.personality}", menu=personality_menu)

        menu.add_command(label="Export route presets", command=self.export_route_presets)

        menu.add_command(label="Import route presets", command=self.import_route_presets)

        route_menu = tk.Menu(menu, tearoff=0, bg="#11182e", fg=WHITE,

                             activebackground="#273456", activeforeground=CYAN)

        for preset in sorted(self.route_presets):

            route_menu.add_command(label=(f"✓ {preset}" if preset == self.active_route_preset else preset),

                                   command=lambda name=preset: self.use_route_preset(name))

        menu.add_cascade(label="Switch patrol preset", menu=route_menu)

        menu.add_command(label="Rescan desktop icons", command=self.rescan_desktop_icons)

        menu.add_command(label="Patrol log", command=self.show_patrol_log)

        menu.add_command(label="Export patrol log CSV", command=self.export_patrol_log)

        icon_menu = tk.Menu(menu, tearoff=0, bg="#11182e", fg=WHITE,

                            activebackground="#273456", activeforeground=CYAN)

        for index, (_x, _y, label) in sorted(

                enumerate(self.icon_targets), key=lambda item: item[1][2].casefold())[:60]:

            icon_menu.add_command(label=label[:40],

                                  command=lambda target=index: self.go_to_icon(target))

        menu.add_cascade(label="Go to desktop icon", menu=icon_menu,

                         state="normal" if self.icon_targets else "disabled")

        menu.add_command(label="Bit Catcher mini-game", command=self.open_game)

        menu.add_command(label="Pet", command=self.pet)

        menu.add_command(label="Sleep / Wake", command=self.toggle_sleep)

        menu.add_command(label="Start 25-minute focus", command=self.start_focus)

        menu.add_command(label="Stop focus timer", command=self.stop_focus)

        menu.add_command(label="Stats", command=self.show_stats)

        menu.add_command(label="Terminal panel", command=self.open_terminal)

        menu.add_command(label="Network check", command=self.network_check)

        menu.add_command(label="Speak", command=self.speak)

        menu.add_command(label="Listen for a command…", command=self.listen_once)

        menu.add_checkbutton(label="Spoken companion", variable=self.voice_var,

                             command=self.toggle_voice_output)

        menu.add_checkbutton(label="Auto-feed from old user temp files",

                             variable=self.auto_feed_var, command=self.toggle_auto_feed)

        menu.add_separator()

        menu.add_command(label="Neon settings…", command=self.open_settings)

        menu.add_command(label="Check for updates now", command=lambda: self.check_for_updates(announce=True))

        menu.add_command(label="Start 25-minute focus", command=self.start_focus)

        menu.add_command(label="Stop focus timer", command=self.stop_focus)

        menu.add_command(label="Stats", command=self.show_stats)

        menu.add_separator()

        menu.add_command(label="Quit", command=self.quit)

        menu.tk_popup(event.x_root, event.y_root)

    def installed_speech_voices(self):

        if os.name != "nt":

            return []

        script = ("Add-Type -AssemblyName System.Speech; "

                  "$s=New-Object System.Speech.Synthesis.SpeechSynthesizer; "

                  "$s.GetInstalledVoices() | ForEach-Object { $_.VoiceInfo.Name }; "

                  "$s.Dispose()")

        try:

            result = subprocess.run(self.powershell(script), capture_output=True,

                                    text=True, timeout=8, check=True,

                                    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))

        except (OSError, subprocess.SubprocessError):

            return []

        names = [line.strip() for line in result.stdout.splitlines() if line.strip()]

        return list(dict.fromkeys(names))

    def open_settings(self):

        existing = getattr(self, "settings_window", None)

        if existing is not None and existing.winfo_exists():

            existing.deiconify()

            existing.lift()

            return

        window = tk.Toplevel(self.root)

        self.settings_window = window

        window.title("Neon settings")

        window.configure(bg="#0b1020")

        window.resizable(False, False)

        window.transient(self.root)

        window.protocol("WM_DELETE_WINDOW", window.withdraw)

        tk.Label(window, text="NEON  /  SETTINGS", bg="#0b1020", fg=CYAN,

                 font=("Segoe UI", 15, "bold"), padx=18, pady=14).pack(anchor="w")

        tk.Label(window, text="Pet glow color", bg="#0b1020", fg=WHITE,
                 font=("Segoe UI", 11, "bold")).pack(anchor="w", padx=20)
        self.glow_theme_var = tk.StringVar(master=window, value=self.glow_theme)

        def update_glow_theme(theme_name):
            if theme_name not in GLOW_PALETTES:
                return
            self.glow_theme = theme_name
            self.save_state()
            self.draw()

        glow_picker = tk.OptionMenu(window, self.glow_theme_var,
                                    *GLOW_PALETTES.keys(), command=update_glow_theme)
        glow_picker.configure(bg="#172441", fg=WHITE, activebackground="#273456",
                              activeforeground=CYAN, relief="flat", bd=0,
                              highlightthickness=0, font=("Segoe UI", 10),
                              anchor="w", width=30)
        glow_picker["menu"].configure(bg="#11182e", fg=WHITE,
                                      activebackground="#273456",
                                      activeforeground=CYAN)
        glow_picker.pack(anchor="w", padx=20, pady=(4, 12))

        tk.Label(window, text="Movement pace", bg="#0b1020", fg=WHITE,
                 font=("Segoe UI", 11, "bold")).pack(anchor="w", padx=20)
        movement_label = tk.Label(
            window, text=f"{round(self.movement_speed * 100)}%",
            bg="#0b1020", fg="#9db0d4", font=("Segoe UI", 9))
        movement_label.pack(anchor="w", padx=20, pady=(2, 0))

        def update_movement_speed(value):
            self.movement_speed = int(float(value)) / 100
            movement_label.configure(text=f"{round(self.movement_speed * 100)}%")
            if getattr(self, "settings_save_job", None) is not None:
                try:
                    self.root.after_cancel(self.settings_save_job)
                except tk.TclError:
                    pass
            self.settings_save_job = self.root.after(400, self.save_state)

        self.movement_speed_var = tk.IntVar(
            master=window, value=round(self.movement_speed * 100))
        tk.Scale(window, from_=50, to=200, resolution=10, orient="horizontal",
                 variable=self.movement_speed_var, command=update_movement_speed,
                 showvalue=False, length=280, bg="#0b1020", fg=WHITE,
                 troughcolor="#192641", activebackground=CYAN,
                 highlightthickness=0, bd=0).pack(padx=18, pady=(4, 10))

        tk.Label(window, text="Menu text size", bg="#0b1020", fg=WHITE,

                 font=("Segoe UI", 11, "bold")).pack(anchor="w", padx=20)

        size_label = tk.Label(window, bg="#0b1020", fg="#9db0d4",

                               font=("Segoe UI", 9))

        size_label.pack(anchor="w", padx=20, pady=(2, 0))

        def update_menu_size(value):

            self.menu_font_points = int(float(value))

            size_label.configure(text=f"{self.menu_font_points} pt added")

            try:

                self.root.tk.call("font", "configure", "TkMenuFont", "-size",

                                  self.menu_font_base_size + self.menu_font_points)

            except tk.TclError:

                return

            if getattr(self, "settings_save_job", None) is not None:

                try:

                    self.root.after_cancel(self.settings_save_job)

                except tk.TclError:

                    pass

            self.settings_save_job = self.root.after(400, self.save_state)

        self.menu_font_var = tk.IntVar(master=window, value=self.menu_font_points)

        tk.Scale(window, from_=0, to=25, resolution=1, orient="horizontal",

                 variable=self.menu_font_var, command=update_menu_size,

                 showvalue=False, length=280, bg="#0b1020", fg=WHITE,

                 troughcolor="#192641", activebackground=CYAN, highlightthickness=0,

                 bd=0).pack(padx=18, pady=(4, 10))

        tk.Label(window, text="Speech pace", bg="#0b1020", fg=WHITE,

                 font=("Segoe UI", 11, "bold")).pack(anchor="w", padx=20)

        rate_label = tk.Label(window, bg="#0b1020", fg="#9db0d4",

                              font=("Segoe UI", 9))

        rate_label.pack(anchor="w", padx=20, pady=(2, 0))

        def update_voice_rate(value):

            self.voice_rate = int(float(value))

            pace = "slower" if self.voice_rate < 0 else "faster" if self.voice_rate > 0 else "normal"

            rate_label.configure(text=f"{pace.title()} ({self.voice_rate:+d})")

            if getattr(self, "settings_save_job", None) is not None:

                try:

                    self.root.after_cancel(self.settings_save_job)

                except tk.TclError:

                    pass

            self.settings_save_job = self.root.after(400, self.save_state)

        self.voice_rate_var = tk.IntVar(master=window, value=self.voice_rate)

        tk.Scale(window, from_=-10, to=10, resolution=1, orient="horizontal",

                 variable=self.voice_rate_var, command=update_voice_rate,

                 showvalue=False, length=280, bg="#0b1020", fg=WHITE,

                 troughcolor="#192641", activebackground=PURPLE, highlightthickness=0,

                 bd=0).pack(padx=18, pady=(4, 10))

        tk.Label(window, text="Speech volume", bg="#0b1020", fg=WHITE,

                 font=("Segoe UI", 11, "bold")).pack(anchor="w", padx=20)

        volume_label = tk.Label(window, bg="#0b1020", fg="#9db0d4",

                                font=("Segoe UI", 9))

        volume_label.pack(anchor="w", padx=20, pady=(2, 0))

        def update_voice_volume(value):

            self.voice_volume = int(float(value))

            volume_label.configure(text=f"{self.voice_volume}%")

            if getattr(self, "settings_save_job", None) is not None:

                try:

                    self.root.after_cancel(self.settings_save_job)

                except tk.TclError:

                    pass

            self.settings_save_job = self.root.after(400, self.save_state)

        self.voice_volume_var = tk.IntVar(master=window, value=self.voice_volume)

        tk.Scale(window, from_=0, to=100, resolution=1, orient="horizontal",

                 variable=self.voice_volume_var, command=update_voice_volume,

                 showvalue=False, length=280, bg="#0b1020", fg=WHITE,

                 troughcolor="#192641", activebackground=CYAN,

                 highlightthickness=0, bd=0).pack(padx=18, pady=(4, 10))

        tk.Label(window, text="Speech voice", bg="#0b1020", fg=WHITE,

                 font=("Segoe UI", 11, "bold")).pack(anchor="w", padx=20)

        voice_names = self.installed_speech_voices()

        choices = ["System default"] + voice_names

        selected_voice = self.voice_name if self.voice_name in voice_names else "System default"

        if selected_voice == "System default" and self.voice_name:

            self.voice_name = ""

            self.save_state()

        self.voice_choice = tk.StringVar(master=window, value=selected_voice)

        def choose_voice(selection):

            self.voice_name = "" if selection == "System default" else selection

            self.save_state()

        voice_picker = tk.OptionMenu(window, self.voice_choice, *choices,

                                     command=choose_voice)

        voice_picker.configure(bg="#172441", fg=WHITE, activebackground="#273456",

                               activeforeground=CYAN, relief="flat", bd=0,

                               highlightthickness=0, font=("Segoe UI", 10),

                               anchor="w", width=30)

        voice_picker["menu"].configure(bg="#11182e", fg=WHITE,

                                       activebackground="#273456",

                                       activeforeground=CYAN)

        voice_picker.pack(anchor="w", padx=20, pady=(4, 12))

        tk.Button(

            window, text="▶  Preview voice",

            command=lambda: self.speak("Hi, I'm Neon. This is my current voice pace."),

            bg="#172441", fg=CYAN, activebackground="#273456",

            activeforeground=WHITE, relief="flat", bd=0,

            font=("Segoe UI", 10, "bold"), padx=12, pady=7,

        ).pack(anchor="w", padx=20, pady=(0, 12))

        tk.Checkbutton(window, text="Spoken companion", variable=self.voice_var,

                       command=self.toggle_voice_output, bg="#0b1020", fg=WHITE,

                       activebackground="#0b1020", activeforeground=CYAN,

                       selectcolor="#192641", font=("Segoe UI", 10)).pack(

                           anchor="w", padx=18, pady=4)

        tk.Checkbutton(window, text="Auto-feed from old user temp files",

                       variable=self.auto_feed_var, command=self.toggle_auto_feed,

                       bg="#0b1020", fg=WHITE, activebackground="#0b1020",

                       activeforeground=CYAN, selectcolor="#192641",

                       font=("Segoe UI", 10)).pack(anchor="w", padx=18, pady=4)

        tk.Label(window, text="Auto-feed check interval", bg="#0b1020", fg=WHITE,
                 font=("Segoe UI", 11, "bold")).pack(anchor="w", padx=20)
        feed_interval_label = tk.Label(
            window, text=f"Every {self.auto_feed_interval_minutes} minutes",
            bg="#0b1020", fg="#9db0d4", font=("Segoe UI", 9))
        feed_interval_label.pack(anchor="w", padx=20, pady=(2, 0))

        def update_feed_interval(value):
            self.auto_feed_interval_minutes = int(float(value))
            feed_interval_label.configure(
                text=f"Every {self.auto_feed_interval_minutes} minutes")
            if getattr(self, "settings_save_job", None) is not None:
                try:
                    self.root.after_cancel(self.settings_save_job)
                except tk.TclError:
                    pass
            self.settings_save_job = self.root.after(400, self.save_state)

        self.feed_interval_var = tk.IntVar(
            master=window, value=self.auto_feed_interval_minutes)
        tk.Scale(window, from_=5, to=60, resolution=5, orient="horizontal",
                 variable=self.feed_interval_var, command=update_feed_interval,
                 showvalue=False, length=280, bg="#0b1020", fg=WHITE,
                 troughcolor="#192641", activebackground=CYAN,
                 highlightthickness=0, bd=0).pack(padx=18, pady=(4, 10))

        tk.Label(window, text="Auto-feed uses the same limited temp/cache scan as Junk Snack.",

                 bg="#0b1020", fg="#8192b2", font=("Segoe UI", 8),

                 padx=20, pady=10).pack(anchor="w")

    def toolbar_action(self):

        rel_x = self.canvas.winfo_pointerx() - self.root.winfo_rootx()

        if rel_x < self.width / 3:

            self.feed()

        elif rel_x < self.width * 2 / 3:

            self.play()

        else:

            self.popup(type("Event", (), {"x_root": self.canvas.winfo_pointerx(),

                                           "y_root": self.canvas.winfo_pointery()})())

    def say(self, text):

        self.message = text

        self.message_ticks = 75

        if (self.voice_enabled and os.name == "nt" and self.desktop_visible

                and self.frame >= self.next_auto_speech_frame):

            self.next_auto_speech_frame = self.frame + 600

            threading.Thread(target=self._speak_worker, args=(str(text)[:220],),

                             daemon=True).start()

    def pet(self):

        self.mood = min(100, self.mood + 9)

        self.gain_xp(1)

        self.mode = "happy"

        self.affection_until = self.frame + 40

        self.wave_until = self.frame + 60

        self.say(random.choice(("hehe!", "more scritches!", "<3", "best human.")))

    def open_terminal(self):

        win = tk.Toplevel(self.root)

        win.title("Neon // Read-only Terminal")

        win.geometry("680x420")

        win.configure(bg="#0c1021")

        tk.Label(win, text="NEON CONSOLE  •  project folder only",

                 bg="#0c1021", fg=CYAN, font=("Consolas", 16, "bold")).pack(anchor="w", padx=12, pady=(12, 4))

        output = tk.Text(win, bg="#090e1c", fg=WHITE, insertbackground=CYAN,

                         font=("Consolas", 15), relief="flat", wrap="word", height=18)

        output.pack(fill="both", expand=True, padx=12, pady=6)

        output.insert("end", "Type help to see available commands.\n")

        output.configure(state="disabled")

        command = tk.Entry(win, bg="#11182e", fg=WHITE, insertbackground=CYAN,

                           font=("Consolas", 15), relief="flat")

        command.pack(fill="x", padx=12, pady=(0, 12))

        def write(text):

            output.configure(state="normal")

            output.insert("end", f"\n> {command.get().strip()}\n{text}\n")

            output.see("end")

            output.configure(state="disabled")

            command.delete(0, "end")

        def run_command(_event=None):

            typed = command.get().strip()

            cmd = typed.lower()

            if cmd == "help":

                result = "Commands: help, status, pwd, ls, python-version, git-status, network, repair-code, repair-save"

            elif cmd == "status":

                result = (f"Neon Lv {self.level} | hunger {self.hunger:.0f}% | "

                          f"mood {self.mood:.0f}% | energy {self.energy:.0f}%")

            elif cmd == "pwd":

                result = str(Path(__file__).resolve().parent)

            elif cmd == "ls":

                try:

                    result = "\n".join(sorted(item.name for item in Path(__file__).resolve().parent.iterdir())) or "(empty)"

                except OSError as error:

                    result = f"Can't list project folder: {error}"

            elif cmd == "python-version":

                result = sys.version.split()[0]

            elif cmd == "git-status":

                try:

                    proc = subprocess.run(["git", "status", "--short"],

                                          cwd=Path(__file__).resolve().parent,

                                          capture_output=True, text=True, timeout=4,

                                          check=False, shell=False)

                    result = proc.stdout.strip() or "Working tree clean."

                    if proc.returncode and proc.stderr:

                        result += "\n" + proc.stderr.strip()

                except (OSError, subprocess.SubprocessError) as error:

                    result = f"Git status unavailable: {error}"

            elif cmd == "network":

                result = self.network_status()

            elif cmd == "repair-code":

                result = self.repair_code()

            elif cmd == "repair-save":

                self.save_state()

                result = "Pet save data rewritten from the current in-memory state."

            elif not typed:

                return

            else:

                result = "Command not allowed. Type help for the read-only command list."

            write(result)

        command.bind("<Return>", run_command)

        command.focus_set()

    def repair_code(self):

        source = Path(__file__).resolve()

        try:

            ast.parse(source.read_text(encoding="utf-8"))

            return "Python syntax check passed; no code repair is needed."

        except (OSError, SyntaxError) as error:

            try:

                backup_text = CODE_BACKUP_PATH.read_text(encoding="utf-8")

                ast.parse(backup_text)

            except (OSError, SyntaxError) as backup_error:

                return f"Repair unavailable: no valid startup snapshot ({backup_error})."

            if not messagebox.askyesno(

                    "Neon // Repair Code",

                    "Neon found a Python syntax error. Restore the startup snapshot?\n"

                    f"\n{error}", parent=self.root):

                return "Code repair cancelled."

            try:

                repair = source.with_suffix(".repair.tmp")

                repair.write_text(backup_text, encoding="utf-8")

                repair.replace(source)

                return "Restored the startup snapshot. Restart Neon to load the repaired code."

            except OSError as write_error:

                return f"Could not restore the code file: {write_error}"

    def network_status(self):

        host = "example.com"

        started = time.monotonic()

        try:

            with socket.create_connection((host, 443), timeout=4) as connection:

                with ssl.create_default_context().wrap_socket(connection, server_hostname=host):

                    pass

            elapsed_ms = round((time.monotonic() - started) * 1000)

            return f"HTTPS connection to {host} succeeded ({elapsed_ms} ms)."

        except (OSError, ssl.SSLError) as error:

            return f"Network check failed: {error}"

    @staticmethod

    def powershell(script):

        encoded = base64.b64encode(script.encode("utf-16le")).decode("ascii")

        return ["powershell.exe", "-NoLogo", "-NoProfile", "-NonInteractive",

                "-WindowStyle", "Hidden", "-EncodedCommand", encoded]

    def toggle_voice_output(self):

        self.voice_enabled = bool(self.voice_var.get())

        if self.voice_enabled:

            self.next_auto_speech_frame = self.frame

        self.save_state()

        self.say("spoken companion enabled" if self.voice_enabled else "spoken companion muted")

    def speech_output_error(self):

        self.voice_enabled = False

        self.voice_var.set(False)

        self.say("Windows speech output isn't available.")

        self.save_state()

    def speak(self, text=None):

        phrase = (text or self.message or "Hi, I'm Neon.")[:400]

        if os.name != "nt":

            self.say("Voice output is available on Windows.")

            return

        threading.Thread(target=self._speak_worker, args=(phrase,), daemon=True).start()

    def _speak_worker(self, phrase):

        if not self.voice_lock.acquire(blocking=False):

            return

        script = ("$ErrorActionPreference='Stop'; Add-Type -AssemblyName System.Speech; "

                  "$payload=[Console]::In.ReadToEnd() | ConvertFrom-Json; "

                  "$voice=New-Object System.Speech.Synthesis.SpeechSynthesizer; "

                  "if ($payload.voice) { $voice.SelectVoice($payload.voice) }; "

                  f"$voice.Rate={self.voice_rate}; $voice.Volume={self.voice_volume}; "

                  "$voice.Speak([string]$payload.text); $voice.Dispose()")

        try:

            payload = json.dumps({"voice": self.voice_name, "text": phrase})

            subprocess.run(self.powershell(script), input=payload, capture_output=True,

                           text=True, timeout=20, check=True,

                           creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))

        except (OSError, subprocess.SubprocessError):

            try:

                self.root.after(0, self.speech_output_error)

            except tk.TclError:

                pass

        finally:

            self.voice_lock.release()

    def listen_once(self):

        if os.name != "nt":

            self.say("Speech recognition is available on Windows.")

            return

        self.say("Listening for 8 seconds. Say a command to Neon.")

        self.root.bell()

        threading.Thread(target=self._listen_worker, daemon=True).start()

    def _listen_worker(self):

        script = (

            "$ErrorActionPreference='Stop'; Add-Type -AssemblyName System.Speech; "

            "$engine=New-Object System.Speech.Recognition.SpeechRecognitionEngine; "

            "$engine.LoadGrammar((New-Object System.Speech.Recognition.DictationGrammar)); "

            "$engine.SetInputToDefaultAudioDevice(); "

            "$result=$engine.Recognize([TimeSpan]::FromSeconds(8)); "

            "if ($null -ne $result) { [Console]::Out.WriteLine($result.Text) }; "

            "$engine.Dispose()")

        try:

            result = subprocess.run(self.powershell(script), capture_output=True,

                                    text=True, timeout=13, check=True,

                                    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))

            recognized = result.stdout.strip()

            self.root.after(0, self.handle_voice_text, recognized)

        except (OSError, subprocess.SubprocessError) as error:

            self.root.after(0, self.voice_error, str(error))

    def voice_error(self, detail):

        self.say("Couldn't hear you. Check your microphone and Windows speech settings.")

        messagebox.showinfo("Neon // Voice", f"Speech recognition couldn't start.\n{detail}",

                            parent=self.root)

    def handle_voice_text(self, recognized):

        if not recognized:

            self.say("I didn't catch that. Try again!")

            return

        phrase = recognized.lower().strip(" .,!?")

        if phrase.startswith("neon "):

            phrase = phrase[5:].strip()

        if phrase in ("feed", "eat", "snack"):

            self.feed()

        elif phrase in ("play", "game"):

            self.play()

        elif phrase in ("pet", "hello", "hi"):

            self.pet()

        elif phrase == "sleep":

            if not self.sleeping:

                self.toggle_sleep()

        elif phrase == "wake":

            if self.sleeping:

                self.toggle_sleep()

        elif phrase == "status":

            self.show_stats()

        elif phrase == "network":

            self.say(self.network_status())

        else:

            self.say(f"I heard: {recognized[:24]}")

        self.draw()

    def toggle_auto_feed(self):

        self.auto_feed = bool(self.auto_feed_var.get())

        if self.auto_feed_job is not None:

            try:

                self.root.after_cancel(self.auto_feed_job)

            except tk.TclError:

                pass

            self.auto_feed_job = None

        if self.auto_feed:

            self.auto_feed_job = self.root.after(self.auto_feed_interval_minutes * 60_000, self.auto_feed_tick)

            self.say("auto-feed enabled. I'll snack when I'm hungry.")

        else:

            self.say("auto-feed paused.")

        self.save_state()

    def user_temp_root(self):

        home = Path.home().resolve()

        local_appdata = os.environ.get("LOCALAPPDATA")

        candidates = ([Path(local_appdata) / "Temp"] if local_appdata

                      else [Path(tempfile.gettempdir())])

        candidates.append(Path(tempfile.gettempdir()))

        for candidate in candidates:

            try:

                root = candidate.resolve()

                if (root.is_dir() and root != home

                        and os.path.commonpath((str(home), str(root))) == str(home)):

                    return root

            except (OSError, ValueError):

                continue

        return None

    def auto_feed_tick(self):

        self.auto_feed_job = None

        if self.auto_feed and self.hunger < 55:

            root = self.user_temp_root()

            cutoff = time.time() - 7 * 24 * 60 * 60

            candidates = []

            if root is not None:

                try:

                    for path in root.rglob("*"):

                        try:

                            info = path.lstat()

                            if (stat.S_ISREG(info.st_mode) and info.st_mtime < cutoff

                                    and os.path.commonpath((str(root), str(path.resolve()))) == str(root)):

                                candidates.append((info.st_mtime, path, info.st_size))

                        except (OSError, ValueError):

                            continue

                except OSError:

                    candidates = []

            candidates.sort(key=lambda item: item[0])

            removed = 0

            removed_bytes = 0

            for _modified, path, _size in candidates:

                if removed >= 3:

                    break

                try:

                    info = path.lstat()

                    if (stat.S_ISREG(info.st_mode) and info.st_mtime < cutoff

                            and os.path.commonpath((str(root), str(path.resolve()))) == str(root)):

                        path.unlink()

                        removed += 1

                        removed_bytes += info.st_size

                except (OSError, ValueError):

                    continue

            if removed:

                self.hunger = min(100, self.hunger + min(35, 10 + 5 * removed))

                self.mood = min(100, self.mood + 4)

                self.gain_xp(min(3, removed))

                self.mode = "eat"

                self.say(f"auto-snack! I crunched {removed} old temp files.")

                self.save_state()

                self.draw()

        if self.auto_feed:

            self.auto_feed_job = self.root.after(self.auto_feed_interval_minutes * 60_000, self.auto_feed_tick)

    def network_check(self):

        result = self.network_status()

        self.say("network online." if "succeeded" in result else "network check failed.")

        messagebox.showinfo("Neon // Network", result, parent=self.root)

    def check_for_updates(self, announce=False):

        self.save_state()

        if apply_zip_update():

            self.root.destroy()

            return

        if announce:

            self.say(f"Neon is up to date (v{APP_VERSION}).")

        self.root.after(5 * 60 * 1000, self.check_for_updates)

    def feed_on_junk(self):

        """Offer old files from a small allowlist of rebuildable temp/cache folders."""

        roots = [("Your temp folder", Path(tempfile.gettempdir()))]

        local_appdata = os.environ.get("LOCALAPPDATA")

        windows_dir = os.environ.get("WINDIR")

        program_data = os.environ.get("ProgramData")

        if local_appdata:

            local = Path(local_appdata)

            roots.extend([

                ("DirectX shader cache", local / "D3DSCache"),

                ("NVIDIA shader cache", local / "NVIDIA" / "DXCache"),

                ("App crash dumps", local / "CrashDumps"),

                ("Windows error report archive", local / "Microsoft" / "Windows" / "WER" / "ReportArchive"),

                ("Windows error report queue", local / "Microsoft" / "Windows" / "WER" / "ReportQueue"),

            ])

        if windows_dir:

            roots.append(("Windows temp folder", Path(windows_dir) / "Temp"))

        if program_data:

            machine_wer = Path(program_data) / "Microsoft" / "Windows" / "WER"

            roots.extend([

                ("System error report archive", machine_wer / "ReportArchive"),

                ("System error report queue", machine_wer / "ReportQueue"),

            ])

        allowed_roots = []

        seen_roots = set()

        for label, folder in roots:

            try:

                resolved_root = folder.resolve()

                key = os.path.normcase(str(resolved_root))

                if resolved_root.is_dir() and key not in seen_roots:

                    allowed_roots.append((label, resolved_root))

                    seen_roots.add(key)

            except OSError:

                continue

        cutoff = time.time() - 7 * 24 * 60 * 60

        candidates = []

        total_bytes = 0

        per_root = {}

        for label, root in allowed_roots:

            try:

                for path in root.rglob("*"):

                    try:

                        info = path.lstat()

                        if not stat.S_ISREG(info.st_mode):

                            continue

                        resolved = path.resolve()

                        if os.path.commonpath((str(root), str(resolved))) != str(root):

                            continue

                        if info.st_mtime >= cutoff:

                            continue

                        candidates.append((path, root, label))

                        total_bytes += info.st_size

                        count, size = per_root.get(label, (0, 0))

                        per_root[label] = (count + 1, size + info.st_size)

                    except (OSError, ValueError):

                        continue

            except OSError:

                # Some protected system folders may be unreadable without admin rights.

                continue

        if not candidates:

            messagebox.showinfo(

                "Neon // Junk Snack",

                "No files older than 7 days were found in the selected temp/cache folders.\n"

                "Windows-protected files may be inaccessible.", parent=self.root)

            self.say("no old junk found...")

            return

        # Review exact candidates first. Nothing is selected until the user chooses.

        review = tk.Toplevel(self.root)

        review.title("Neon // Review Junk Snacks")

        review.geometry("760x440")

        review.configure(bg="#0c1021")

        review.transient(self.root)

        review.attributes("-topmost", True)

        tk.Label(review, text=f"{len(candidates)} old files found • select what Neon may eat",

                 bg="#0c1021", fg=CYAN, font=("Consolas", 16, "bold")).pack(anchor="w", padx=12, pady=(12, 4))

        tk.Label(review, text="Nothing is selected by default. Files are rechecked before deletion.",

                 bg="#0c1021", fg=MUTED, font=("Consolas", 14)).pack(anchor="w", padx=12, pady=(0, 8))

        listing = tk.Frame(review, bg="#0c1021")

        listing.pack(fill="both", expand=True, padx=12)

        scrollbar = tk.Scrollbar(listing)

        scrollbar.pack(side="right", fill="y")

        file_list = tk.Listbox(listing, selectmode=tk.EXTENDED, yscrollcommand=scrollbar.set,

                               bg="#11182e", fg=WHITE, selectbackground="#273456",

                               selectforeground=CYAN, font=("Consolas", 14),

                               activestyle="dotbox", exportselection=False)

        file_list.pack(side="left", fill="both", expand=True)

        scrollbar.config(command=file_list.yview)

        for path, _root, label in candidates:

            try:

                info = path.lstat()

                age_days = max(0, int((time.time() - info.st_mtime) / 86400))

                file_list.insert(tk.END, f"{label}  |  {path}  |  {info.st_size / 1024:.1f} KB  |  {age_days}d old")

            except OSError:

                file_list.insert(tk.END, f"{label}  |  {path}  |  changed since scan")

        selected = {"items": None}

        controls = tk.Frame(review, bg="#0c1021")

        controls.pack(fill="x", padx=12, pady=12)

        def choose_all():

            file_list.selection_set(0, tk.END)

        def choose_none():

            file_list.selection_clear(0, tk.END)

        def accept_selection():

            indices = file_list.curselection()

            if not indices:

                messagebox.showinfo("Neon // Junk Snack", "Select at least one file first.", parent=review)

                return

            selected["items"] = [candidates[index] for index in indices]

            review.destroy()

        tk.Button(controls, text="Select all", command=choose_all, bg="#171d34", fg=CYAN,

                  relief="flat", padx=10, pady=7).pack(side="left")

        tk.Button(controls, text="Clear", command=choose_none, bg="#171d34", fg=MUTED,

                  relief="flat", padx=10, pady=7).pack(side="left", padx=6)

        tk.Button(controls, text="Cancel", command=review.destroy, bg="#171d34", fg=WHITE,

                  relief="flat", padx=10, pady=7).pack(side="right")

        tk.Button(controls, text="Feed selected files…", command=accept_selection,

                  bg="#203247", fg=CYAN, relief="flat", padx=12, pady=7).pack(side="right", padx=6)

        review.protocol("WM_DELETE_WINDOW", review.destroy)

        review.grab_set()

        self.root.wait_window(review)

        candidates = selected["items"]

        if not candidates:

            self.say("snack scan cancelled.")

            return

        selected_bytes = 0

        for path, _root, _label in candidates:

            try:

                selected_bytes += path.lstat().st_size

            except OSError:

                pass

        confirm = messagebox.askyesno(

            "Neon // Junk Snack",

            f"Neon is ready to delete {len(candidates)} selected files "

            f"({selected_bytes / (1024 * 1024):.1f} MiB). Continue?",

            parent=self.root)

        if not confirm:

            self.say("snack deletion cancelled.")

            return

        removed = 0

        removed_bytes = 0

        for path, root, _label in candidates:

            try:

                info = path.lstat()

                resolved = path.resolve()

                if (not stat.S_ISREG(info.st_mode)

                        or os.path.commonpath((str(root), str(resolved))) != str(root)

                        or info.st_mtime >= cutoff):

                    continue

                path.unlink()

                removed += 1

                removed_bytes += info.st_size

            except (OSError, ValueError):

                continue

        self.hunger = min(100, self.hunger + min(45, 12 + removed * 2))

        self.mood = min(100, self.mood + 8)

        self.gain_xp(min(10, removed))

        self.say(f"crunched {removed} junk files! +{removed_bytes // 1024} KB")

        self.save_state()

        self.draw()

        skipped = len(candidates) - removed

        messagebox.showinfo(

            "Neon // Junk Snack",

            f"Neon crunched {removed} files ({removed_bytes / (1024 * 1024):.1f} MiB)."

            + (f"\n{skipped} files were skipped because they changed or were in use." if skipped else ""),

            parent=self.root)

    def feed(self):

        self.hunger = min(100, self.hunger + 32)

        self.mood = min(100, self.mood + 5)

        self.gain_xp(2)

        self.mode = "eat"

        self.say(random.choice(("byte-bites!!", "nom nom", "delicious data.")))

    def play(self):

        if self.energy < 12:

            self.say("battery low... charge me")

            return

        self.energy = max(0, self.energy - 14)

        self.mood = min(100, self.mood + 20)

        self.gain_xp(3)

        self.mode = "play"

        self.say(random.choice(("catch the neon!", "combo x100!", "zoomies!")))

    def toggle_sleep(self):

        self.sleeping = not self.sleeping

        self.mode = "sleep" if self.sleeping else "idle"

        self.say("zzz..." if self.sleeping else "back online!")

    def gain_xp(self, amount):

        old_level = self.level

        self.xp += max(0, int(amount))

        if self.level > old_level:

            self.mode = "happy"

            self.say(f"level up! Neon evolved to level {self.level}!")

    def open_game(self):

        if self.game_window is not None:

            try:

                self.game_window.lift()

                return

            except tk.TclError:

                self.game_window = None

        win = tk.Toplevel(self.root)

        self.game_window = win

        win.title("Neon // Bit Catcher")

        win.configure(bg="#0c1021")

        win.resizable(False, False)

        game = tk.Canvas(win, width=340, height=400, bg="#0c1021",

                         highlightthickness=1, highlightbackground=CYAN)

        game.pack(padx=12, pady=(12, 4))

        tk.Label(win, text="Move with ← → or A / D • Catch green bits, dodge red bugs",

                 bg="#0c1021", fg=MUTED, font=("Consolas", 13)).pack(pady=(0, 10))

        state = {"x": 170.0, "items": [], "score": 0, "lives": 3, "tick": 0,

                 "keys": set(), "over": False}

        def key_down(event):

            state["keys"].add(event.keysym.lower())

        def key_up(event):

            state["keys"].discard(event.keysym.lower())

        win.bind("<KeyPress>", key_down)

        win.bind("<KeyRelease>", key_up)

        win.focus_force()

        def close_game():

            self.game_window = None

            win.destroy()

        def finish():

            if state["over"]:

                return

            state["over"] = True

            self.best = max(self.best, state["score"])

            self.gain_xp(state["score"] // 2 + 1)

            self.mood = min(100, self.mood + min(20, state["score"]))

            self.energy = max(0, self.energy - 8)

            self.say(f"game over! {state['score']} bits")

            self.save_state()

            game.create_text(170, 188, text="GAME OVER", fill=WHITE,

                             font=("Consolas", 22, "bold"), tags="overlay")

            game.create_text(170, 222, text="Click to close • XP earned!", fill=CYAN,

                             font=("Consolas", 10), tags="overlay")

            game.bind("<Button-1>", lambda _event: close_game())

        def step():

            if not win.winfo_exists() or state["over"]:

                return

            state["tick"] += 1

            if state["keys"] & {"left", "a"}:

                state["x"] -= 7

            if state["keys"] & {"right", "d"}:

                state["x"] += 7

            state["x"] = max(25, min(315, state["x"]))

            if state["tick"] % 24 == 0:

                kind = "bug" if random.random() < 0.25 else "bit"

                state["items"].append({"x": random.randint(15, 325), "y": -8,

                                       "kind": kind, "speed": random.uniform(2.2, 4.8)})

            for item in state["items"][:]:

                item["y"] += item["speed"]

                if item["y"] >= 330 and abs(item["x"] - state["x"]) < 32:

                    state["items"].remove(item)

                    if item["kind"] == "bit":

                        state["score"] += 1

                    else:

                        state["lives"] -= 1

                elif item["y"] > 410:

                    state["items"].remove(item)

            game.delete("frame")

            game.create_text(12, 12, anchor="nw",

                             text=f"BITS {state['score']}     LIVES {'♥ ' * state['lives']}",

                             fill=CYAN, font=("Consolas", 11, "bold"), tags="frame")

            for item in state["items"]:

                color = PINK if item["kind"] == "bug" else "#6cffb0"

                glyph = "×" if item["kind"] == "bug" else "1"

                game.create_text(item["x"], item["y"], text=glyph, fill=color,

                                 font=("Consolas", 17, "bold"), tags="frame")

            game.create_rectangle(state["x"] - 23, 342, state["x"] + 23, 357,

                                  fill=PURPLE, outline=CYAN, width=2, tags="frame")

            game.create_text(state["x"], 350, text="N", fill=WHITE,

                             font=("Consolas", 10, "bold"), tags="frame")

            if state["lives"] <= 0:

                finish()

            else:

                win.after(33, step)

        win.protocol("WM_DELETE_WINDOW", close_game)

        step()

    def start_focus(self):

        self.focus_end = time.time() + 25 * 60

        self.say("focus time. you got this!")

    def stop_focus(self):

        self.focus_end = None

        self.say("focus timer stopped.")

    def show_stats(self):

        self.say(f"Lv {self.level}  XP {self.xp}  best {self.best}")

    def desktop_is_foreground(self):

        if os.name != "nt":

            return True

        try:

            user32 = ctypes.windll.user32

            user32.GetForegroundWindow.restype = ctypes.wintypes.HWND

            hwnd = user32.GetForegroundWindow()

            if not hwnd:

                return False

            process_id = ctypes.wintypes.DWORD()

            user32.GetWindowThreadProcessId(hwnd, ctypes.byref(process_id))

            if process_id.value == os.getpid():

                return True

            class_name = ctypes.create_unicode_buffer(256)

            user32.GetClassNameW(hwnd, class_name, len(class_name))

            return class_name.value in ("Progman", "WorkerW", "Shell_TrayWnd")

        except (AttributeError, OSError, ValueError):

            return True

    def update_visibility(self):

        show = self.desktop_is_foreground()

        if show and self.window_hidden:

            self.root.deiconify()

            self.toolbar.deiconify()

            self.toolbar.lift()

            self.window_hidden = False

        elif not show and not self.window_hidden:

            self.root.withdraw()

            self.toolbar.withdraw()

            self.window_hidden = True

        return show

    def start_icon_hop(self, target_index=None):

        if not self.icon_targets:

            return

        if target_index is None:

            if self.patrol_route:

                target_index = self.patrol_route[self.route_cursor % len(self.patrol_route)]

                self.route_cursor = (self.route_cursor + 1) % len(self.patrol_route)

            else:

                target_index = self.icon_target_index

        elif target_index in self.patrol_route:

            self.route_cursor = (self.patrol_route.index(target_index) + 1) % len(self.patrol_route)

        target_index = min(max(0, int(target_index)), len(self.icon_targets) - 1)

        self.icon_target_index = target_index

        target = self.icon_targets[target_index][:2]

        self.icon_target_index = (target_index + 1) % len(self.icon_targets)

        if math.dist((self.x, self.y), target) < 36 * self.scale:

            self.next_hop_frame = self.frame + 10

            return

        self.hop_start = (self.x, self.y)

        self.hop_target = target

        self.hop_elapsed = 0.0

        self.hop_duration = (0.55 if self.frame < self.zoomies_until else
                             PERSONALITIES[self.personality]["hop_seconds"]) / self.movement_speed

        self.mode = "hop"

        self.manual_destination = None

        self.facing = 1 if target[0] >= self.x else -1

    def go_to_icon(self, index):

        if not 0 <= index < len(self.icon_targets):

            return

        self.patrol_paused = False

        self.sleeping = False

        self.ceiling_pending = False

        self.manual_destination = None

        self.start_icon_hop(target_index=index)

    def advance_icon_hop(self):

        self.hop_elapsed += TICK_MS / 1000

        progress = min(1.0, self.hop_elapsed / self.hop_duration)

        eased = progress * progress * (3 - 2 * progress)

        start_x, start_y = self.hop_start

        end_x, end_y = self.hop_target

        arc_height = min(80 * self.scale, max(28 * self.scale,

                          math.hypot(end_x - start_x, end_y - start_y) * 0.16))

        self.x = start_x + (end_x - start_x) * eased

        self.y = start_y + (end_y - start_y) * eased - math.sin(math.pi * progress) * arc_height

        if progress >= 1.0:

            self.x, self.y = end_x, end_y

            self.landing_frame = self.frame

            if self.manual_destination == "HOME":

                destination = "HOME"

            elif self.icon_targets:

                destination = self.icon_targets[(self.icon_target_index - 1) % len(self.icon_targets)][2]

            else:

                destination = "DESKTOP"

            self.patrol_log.append({"name": destination[:32],

                                   "time": time.strftime("%Y-%m-%d %H:%M:%S"),

                                   "x": round(self.x), "y": round(self.y)})

            self.patrol_log = self.patrol_log[-30:]

            self.save_state()

            self.route_history.append((round(self.x), round(self.y)))

            self.route_history = self.route_history[-14:]

            if self.ceiling_pending:

                self.ceiling_pending = False

                self.y = 0

                self.mode = "ceiling"

                self.ceiling_until = self.frame + random.randint(180, 300)

                self.next_crawl_frame = self.ceiling_until + PERSONALITIES[self.personality]["crawl_delay"]

            else:

                self.mode = "idle"

                self.next_hop_frame = self.frame + random.randint(*PERSONALITIES[self.personality]["hop_wait"])

    def preview_patrol_route(self):

        route = [index for index in self.patrol_route

                 if 0 <= index < len(self.icon_targets)]

        if not route:

            self.say("choose a route before previewing it")

            return

        window = tk.Toplevel(self.root)

        window.title(f"Neon // Route preview — {self.active_route_preset}")

        window.geometry("790x460")

        window.configure(bg=BG)

        tk.Label(window, text=f"ROUTE PREVIEW // {self.active_route_preset.upper()}",

                 bg=BG, fg=CYAN, font=("Consolas", 18, "bold")).pack(anchor="w", padx=14, pady=(14, 4))

        profile = PERSONALITIES[self.personality]

        estimated = round(len(route) * (profile["hop_seconds"] + sum(profile["hop_wait"]) / 2 * TICK_MS / 1000))

        estimate_text = f"{len(route)} stops  •  estimated lap: about {estimated}s"

        tk.Label(window, text=estimate_text, bg=BG, fg=MUTED,

                 font=("Consolas", 14)).pack(anchor="w", padx=14, pady=(0, 8))

        content = tk.Frame(window, bg=BG)

        content.pack(fill="both", expand=True, padx=14)

        map_canvas = tk.Canvas(content, width=500, height=340, bg="#080d19",

                               highlightthickness=1, highlightbackground="#385272")

        map_canvas.pack(side="left", fill="both", expand=True)

        list_frame = tk.Frame(content, bg=BG)

        list_frame.pack(side="right", fill="y", padx=(12, 0))

        tk.Label(list_frame, text="STOP ORDER", bg=BG, fg=CYAN,

                 font=("Consolas", 15, "bold")).pack(anchor="w", pady=(0, 5))

        stop_list = tk.Listbox(list_frame, width=30, height=17, bg="#080d19", fg=WHITE,

                               selectbackground="#234b70", font=("Consolas", 14), relief="flat")

        stop_list.pack(fill="both", expand=True)

        canvas_width, canvas_height = 500, 340

        margin = 26

        map_scale = min((canvas_width - 2 * margin) / max(1, self.screen_w),

                        (canvas_height - 2 * margin) / max(1, self.screen_h))

        map_width, map_height = self.screen_w * map_scale, self.screen_h * map_scale

        left, top = (canvas_width - map_width) / 2, (canvas_height - map_height) / 2

        map_canvas.create_rectangle(left, top, left + map_width, top + map_height,

                                    outline="#55708f", width=2)

        map_canvas.create_text(left + 5, top + 5, text="DESKTOP", anchor="nw",

                               fill=MUTED, font=("Consolas", 8))

        points = []

        for step, index in enumerate(route, start=1):

            x, y, label = self.icon_targets[index]

            px, py = left + x * map_scale, top + y * map_scale

            points.append((px, py))

            stop_list.insert("end", f"{step:02d}  {label[:20]}")

        if len(points) > 1:

            line = [coordinate for point in points for coordinate in point]

            line.extend(points[0])

            map_canvas.create_line(*line, fill="#9b67ff", width=2,

                                   dash=(5, 3), smooth=True, splinesteps=12,

                                   arrow=tk.LAST)

        for step, ((px, py), index) in enumerate(zip(points, route), start=1):

            map_canvas.create_oval(px - 5, py - 5, px + 5, py + 5,

                                   fill="#47a6f0", outline=WHITE, width=1)

            map_canvas.create_text(px + 8, py - 8, text=str(step), anchor="sw",

                                   fill=CYAN, font=("Consolas", 8, "bold"))

        current_x = left + self.x * map_scale

        current_y = top + self.y * map_scale

        map_canvas.create_oval(current_x - 5, current_y - 5, current_x + 5, current_y + 5,

                               fill=CYAN, outline=WHITE, width=1)

        controls = tk.Frame(window, bg=BG)

        controls.pack(fill="x", padx=14, pady=12)

        def start_route():

            self.route_cursor = 0

            self.patrol_paused = False

            self.sleeping = False

            self.mode = "idle"

            self.start_icon_hop()

            window.destroy()

        tk.Button(controls, text="START THIS ROUTE", command=start_route,

                  bg="#17233c", fg=CYAN, relief="flat").pack(side="right")

        tk.Button(controls, text="CLOSE", command=window.destroy,

                  bg="#17233c", fg=WHITE, relief="flat").pack(side="right", padx=8)

    def export_route_presets(self):

        path = filedialog.asksaveasfilename(

            parent=self.root, title="Export Neon route presets", defaultextension=".json",

            initialfile="neon-routes.json",

            filetypes=(("JSON files", "*.json"), ("All files", "*.*")))

        if not path:

            return

        keys = self.desktop_icon_keys()

        payload = {

            "format": "neon-route-presets-v1",

            "active": self.active_route_preset,

            "presets": {

                name: [keys[index] for index in route if 0 <= index < len(keys)]

                for name, route in self.route_presets.items()

            },

        }

        try:

            Path(path).write_text(json.dumps(payload, indent=2), encoding="utf-8")

        except OSError as error:

            messagebox.showerror("Neon // Routes", f"Couldn't export routes.\n{error}", parent=self.root)

            return

        messagebox.showinfo("Neon // Routes", f"Exported {len(payload['presets'])} presets.", parent=self.root)

    def import_route_presets(self):

        path = filedialog.askopenfilename(

            parent=self.root, title="Import Neon route presets",

            filetypes=(("Neon route JSON", "neon-routes*.json"), ("JSON files", "*.json"),

                       ("All files", "*.*")))

        if not path:

            return

        try:

            if Path(path).stat().st_size > 1024 * 1024:

                raise ValueError("The route file is too large.")

            payload = json.loads(Path(path).read_text(encoding="utf-8"))

            if not isinstance(payload, dict) or payload.get("format") != "neon-route-presets-v1":

                raise ValueError("This is not a Neon route preset file.")

            raw_presets = payload.get("presets")

            if not isinstance(raw_presets, dict):

                raise ValueError("The route file has no preset list.")

        except (OSError, ValueError, TypeError) as error:

            messagebox.showerror("Neon // Routes", f"Couldn't import routes.\n{error}", parent=self.root)

            return

        lookup = {key: index for index, key in enumerate(self.desktop_icon_keys())}

        imported = {}

        for name, keys in list(raw_presets.items())[:24]:

            if not isinstance(name, str) or not name.strip() or not isinstance(keys, list):

                continue

            route = [lookup[key] for key in keys if isinstance(key, str) and key in lookup]

            if route:

                imported[name.strip()[:24]] = list(dict.fromkeys(route))

        if not imported:

            messagebox.showinfo("Neon // Routes", "No imported routes matched icons on this desktop.",

                                parent=self.root)

            return

        self.route_presets.update(imported)

        active = payload.get("active")

        chosen = active if isinstance(active, str) and active in imported else next(iter(imported))

        self.use_route_preset(chosen)

        messagebox.showinfo("Neon // Routes", f"Imported {len(imported)} presets.", parent=self.root)

    def set_personality(self, name):

        if name not in PERSONALITIES:

            return

        self.personality = name

        self.next_crawl_frame = self.frame + PERSONALITIES[name]["crawl_delay"]

        self.next_hop_frame = self.frame

        self.save_state()

        self.say(f"personality: {name}")

    def use_route_preset(self, name):

        route = self.route_presets.get(name)

        if not route:

            self.say("that route has no available icons")

            return

        self.active_route_preset = name

        self.patrol_route = list(route)

        self.route_cursor = 0

        self.save_state()

        self.say(f"route loaded: {name}")

    def apply_desktop_icons(self, new_icons, announce=False):

        old_keys = self.desktop_icon_keys()

        new_icons = list(new_icons)

        new_keys = self.desktop_icon_keys(new_icons)

        old_signature = [(key, round(icon[0]), round(icon[1]))

                         for key, icon in zip(old_keys, self.icon_targets)]

        new_signature = [(key, round(icon[0]), round(icon[1]))

                         for key, icon in zip(new_keys, new_icons)]

        self.icon_scan_busy = False

        if not new_icons and self.icon_targets and not announce:

            return

        if old_signature == new_signature:

            if announce:

                self.say(f"desktop rescanned: {len(self.icon_targets)} icons")

            return

        old_routes = {

            name: [old_keys[i] for i in route if 0 <= i < len(old_keys)]

            for name, route in self.route_presets.items()

        }

        old_current = [old_keys[i] for i in self.patrol_route if 0 <= i < len(old_keys)]

        active = self.active_route_preset

        self.icon_targets = new_icons

        new_lookup = {key: index for index, key in enumerate(new_keys)}

        self.route_presets = {

            name: ([new_lookup[key] for key in new_keys] if name == "All apps"

                   else [new_lookup[key] for key in keys if key in new_lookup])

            for name, keys in old_routes.items()

        }

        self.route_presets.setdefault("All apps", list(range(len(self.icon_targets))))

        self.route_presets["Custom"] = [new_lookup[key] for key in old_current if key in new_lookup]

        self.active_route_preset = active if active in self.route_presets else "Custom"

        self.patrol_route = list(self.route_presets.get(self.active_route_preset, []))

        if not self.patrol_route:

            self.patrol_route = list(range(len(self.icon_targets)))

            self.active_route_preset = "All apps"

        self.route_cursor = 0

        self.icon_target_index = 0

        self.save_state()

        if announce:

            self.say(f"desktop rescanned: {len(self.icon_targets)} icons")

    def rescan_desktop_icons(self):

        if self.icon_scan_busy:

            self.say("icon scan already running")

            return

        self.icon_scan_busy = True

        self.apply_desktop_icons(self.load_desktop_icons(), announce=True)

    def auto_rescan_desktop_icons(self):

        if not self.icon_scan_busy:

            self.icon_scan_busy = True

            threading.Thread(target=self._scan_desktop_icons_worker, daemon=True).start()

        self.root.after(5 * 60 * 1000, self.auto_rescan_desktop_icons)

    def _scan_desktop_icons_worker(self):

        try:

            icons = self.load_desktop_icons()

        except Exception:

            icons = []

        try:

            self.root.after(0, lambda: self.apply_desktop_icons(icons, announce=False))

        except tk.TclError:

            self.icon_scan_busy = False

    def edit_patrol_route(self):

        if not self.icon_targets:

            self.say("no desktop icons found")

            return

        window = tk.Toplevel(self.root)

        window.title("Neon // Patrol route")

        window.geometry("460x520")

        window.configure(bg=BG)

        tk.Label(window, text="CHOOSE AND ORDER PATROL STOPS", bg=BG, fg=CYAN,

                 font=("Consolas", 17, "bold")).pack(anchor="w", padx=14, pady=(14, 4))

        tk.Label(window, text="Select stops, then move them with the arrow buttons.",

                 bg=BG, fg=MUTED, font=("Consolas", 14)).pack(anchor="w", padx=14, pady=(0, 8))

        listing = tk.Listbox(window, selectmode=tk.EXTENDED, exportselection=False,

                             bg="#080d19", fg=WHITE, selectbackground="#234b70",

                             selectforeground=CYAN, font=("Consolas", 15), relief="flat")

        listing.pack(fill="both", expand=True, padx=14, pady=(0, 8))

        route_order = {icon: order for order, icon in enumerate(self.patrol_route)}

        ordered = sorted(enumerate(self.icon_targets),

                         key=lambda item: (route_order.get(item[0], len(route_order)),

                                           item[1][2].casefold()))

        def refresh(selection=()):

            listing.delete(0, "end")

            for _index, (_x, _y, label) in ordered:

                listing.insert("end", label)

            for row in selection:

                if 0 <= row < len(ordered):

                    listing.selection_set(row)

        refresh(row for row, (index, _target) in enumerate(ordered)

                if index in route_order)

        def select_all():

            listing.selection_set(0, "end")

        def move_selected(direction):

            rows = list(listing.curselection())

            if direction < 0:

                for row in rows[:]:

                    if row > 0 and row - 1 not in rows:

                        ordered[row - 1], ordered[row] = ordered[row], ordered[row - 1]

                        rows[rows.index(row)] = row - 1

            else:

                for row in reversed(rows[:]):

                    if row < len(ordered) - 1 and row + 1 not in rows:

                        ordered[row + 1], ordered[row] = ordered[row], ordered[row + 1]

                        rows[rows.index(row)] = row + 1

            refresh(sorted(rows))

        def save_route():

            choices = [ordered[row][0] for row in listing.curselection()]

            if not choices:

                messagebox.showinfo("Neon // Patrol route", "Select at least one icon.", parent=window)

                return

            self.patrol_route = choices

            self.route_cursor = 0

            self.save_state()

            self.say(f"route saved: {len(choices)} stops")

            window.destroy()

        def save_as_preset():

            choices = [ordered[row][0] for row in listing.curselection()]

            if not choices:

                messagebox.showinfo("Neon // Patrol route", "Select at least one icon.", parent=window)

                return

            name = simpledialog.askstring("Neon // Save route", "Preset name:", parent=window)

            if not name or not name.strip():

                return

            name = name.strip()[:24]

            self.route_presets[name] = list(choices)

            self.active_route_preset = name

            self.patrol_route = list(choices)

            self.route_cursor = 0

            self.save_state()

            self.say(f"route preset saved: {name}")

            window.destroy()

        buttons = tk.Frame(window, bg=BG)

        buttons.pack(fill="x", padx=14, pady=(0, 14))

        tk.Button(buttons, text="SELECT ALL", command=select_all,

                  bg="#17233c", fg=CYAN, relief="flat").pack(side="left")

        tk.Button(buttons, text="↑", command=lambda: move_selected(-1),

                  bg="#17233c", fg=CYAN, relief="flat", width=3).pack(side="left", padx=4)

        tk.Button(buttons, text="↓", command=lambda: move_selected(1),

                  bg="#17233c", fg=CYAN, relief="flat", width=3).pack(side="left")

        tk.Button(buttons, text="SAVE ROUTE", command=save_route,

                  bg="#17233c", fg=CYAN, relief="flat").pack(side="right")

    def export_patrol_log(self):

        if not self.patrol_log:

            messagebox.showinfo("Neon // Patrol log", "There are no stops to export yet.", parent=self.root)

            return

        path = filedialog.asksaveasfilename(

            parent=self.root, title="Export Neon patrol log", defaultextension=".csv",

            initialfile=f"neon-patrol-{time.strftime('%Y%m%d-%H%M%S')}.csv",

            filetypes=(("CSV files", "*.csv"), ("All files", "*.*")))

        if not path:

            return

        try:

            with open(path, "w", newline="", encoding="utf-8-sig") as output:

                writer = csv.DictWriter(output, fieldnames=("time", "name", "x", "y"))

                writer.writeheader()

                writer.writerows(self.patrol_log[-30:])

        except OSError as error:

            messagebox.showerror("Neon // Patrol log", f"Couldn't export the log.\n{error}", parent=self.root)

            return

        messagebox.showinfo("Neon // Patrol log", f"Exported {len(self.patrol_log[-30:])} stops.", parent=self.root)

    def show_patrol_log(self):

        window = tk.Toplevel(self.root)

        window.title("Neon // Patrol log")

        window.geometry("560x420")

        window.configure(bg=BG)

        tk.Label(window, text="NEON // RECENT PATROL STOPS", bg=BG, fg=CYAN,

                 font=("Consolas", 18, "bold")).pack(anchor="w", padx=14, pady=(14, 8))

        output = tk.Text(window, bg="#080d19", fg=WHITE, insertbackground=CYAN,

                         font=("Consolas", 15), relief="flat", wrap="none")

        output.pack(fill="both", expand=True, padx=14, pady=(0, 8))

        if not self.patrol_log:

            output.insert("end", "No stops logged yet. Neon records each completed hop.\n")

        else:

            for entry in reversed(self.patrol_log):

                output.insert("end", f"{entry['time']}  {entry['name'][:20]:20}  "

                              f"X:{entry['x']} Y:{entry['y']}\n")

        output.configure(state="disabled")

        tk.Button(window, text="EXPORT CSV", command=self.export_patrol_log,

                  bg="#17233c", fg=CYAN, relief="flat").pack(anchor="e", padx=14, pady=(0, 12))

    def pin_home_perch(self):

        self.home_perch = (round(self.x), round(self.y))

        self.manual_destination = "HOME"

        self.save_state()

        self.say("home perch saved")

    def go_home(self):

        if self.home_perch is None:

            self.say("right-click and pin a home perch first")

            return

        self.patrol_paused = False

        self.sleeping = False

        self.ceiling_pending = False

        self.manual_destination = "HOME"

        self.hop_start = (self.x, self.y)

        self.hop_target = self.home_perch

        self.hop_elapsed = 0.0

        self.hop_duration = (0.55 if self.frame < self.zoomies_until else
                             PERSONALITIES[self.personality]["hop_seconds"]) / self.movement_speed

        self.mode = "hop"

        self.facing = 1 if self.home_perch[0] >= self.x else -1

    def teleport_pet(self):

        if self.teleport_phase is not None:
            return
        self.patrol_paused = False
        self.sleeping = False
        self.ceiling_pending = False
        self.manual_destination = None
        max_x = max(0, self.screen_w - self.width)
        max_y = max(0, self.screen_h - self.height)
        target = (random.randint(0, max_x), random.randint(0, max_y))
        min_distance = math.hypot(max_x, max_y) * 0.22
        for _attempt in range(12):
            if math.dist((self.x, self.y), target) >= min_distance:
                break
            target = (random.randint(0, max_x), random.randint(0, max_y))
        self.teleport_from = (round(self.x), round(self.y))
        self.teleport_target = target
        self.teleport_phase = "depart"
        self.teleport_started_frame = self.frame
        self.teleport_phase_until = self.frame + 16
        self.mode = "teleport_charge"
        self.say("teleport sequence charging!")

    def teleport_echo_image(self, frame_index, opacity):

        if Image is None or ImageTk is None:
            return None
        key = (frame_index, opacity)
        cached = self.teleport_echo_cache.get(key)
        if cached is not None:
            return cached
        path = (Path(__file__).resolve().parent / "assets" /
                f"codex_jump_{self.animation_scale_tag}_{frame_index}.png")
        try:
            with Image.open(path) as source:
                ghost = source.convert("RGBA")
                alpha = ghost.getchannel("A").point(
                    lambda value: value * opacity // 255)
                ghost.putalpha(alpha)
            cached = ImageTk.PhotoImage(ghost, master=self.root)
        except (OSError, tk.TclError, AttributeError):
            return None
        self.teleport_echo_cache[key] = cached
        if len(self.teleport_echo_cache) > 48:
            self.teleport_echo_cache.pop(next(iter(self.teleport_echo_cache)))
        return cached

    def draw_teleport_effect(self):

        if self.teleport_phase is None:
            return
        progress = min(1.0, max(0.0,
                        (self.frame - self.teleport_started_frame) / 16))
        if self.teleport_phase == "depart":
            radius = 12 + 52 * progress
        else:
            radius = 64 * (1 - progress) + 10
        color = GLOW_PALETTES.get(self.glow_theme, CYAN)
        c = self.canvas
        cx, cy = 150, 138
        c.create_oval(cx - radius, cy - radius, cx + radius, cy + radius,
                      outline=color, width=3, tags="teleport")
        inner = radius * 0.68
        c.create_oval(cx - inner, cy - inner, cx + inner, cy + inner,
                      outline=WHITE, width=1, dash=(3, 3), tags="teleport")
        for index in range(8):
            angle = self.frame * 0.18 + index * math.tau / 8
            inner_radius = radius * 0.76
            outer_radius = radius + (7 if index % 2 == 0 else 2)
            c.create_line(cx + math.cos(angle) * inner_radius,
                          cy + math.sin(angle) * inner_radius,
                          cx + math.cos(angle) * outer_radius,
                          cy + math.sin(angle) * outer_radius,
                          fill=PINK if index % 2 else color,
                          width=2, tags="teleport")

    def start_zoomies(self):

        self.patrol_paused = False

        self.sleeping = False

        self.zoomies_until = self.frame + 600

        if self.icon_targets and self.mode == "idle":

            self.next_hop_frame = self.frame

            self.start_icon_hop()

        self.say("zoomies for 30 seconds!")

    def toggle_patrol(self):

        self.patrol_paused = not self.patrol_paused

        if self.patrol_paused:

            self.ceiling_pending = False

            self.mode = "idle"

            self.say("patrol paused")

        else:

            self.next_hop_frame = self.frame

            self.next_crawl_frame = self.frame + PERSONALITIES[self.personality]["crawl_delay"]

            self.say("patrol resumed")

    def begin_ceiling_crawl(self):

        self.patrol_paused = False

        self.sleeping = False

        self.ceiling_pending = True

        self.hop_start = (self.x, self.y)

        self.hop_target = (self.x, 0)

        self.hop_elapsed = 0.0

        self.hop_duration = 0.9 / self.movement_speed

        self.mode = "hop"

        self.next_crawl_frame = self.frame + PERSONALITIES[self.personality]["crawl_delay"]

    def return_to_patrol(self):

        self.ceiling_pending = False

        self.mode = "idle"

        self.next_crawl_frame = self.frame + PERSONALITIES[self.personality]["crawl_delay"]

        if self.icon_targets:

            self.next_hop_frame = self.frame

            self.start_icon_hop()

    def tick(self):

        self.frame += 1

        if self.frame % 10 == 0:

            self.desktop_visible = self.update_visibility()

        self.hunger = max(0, self.hunger - 0.0006)

        if self.sleeping:

            self.energy = min(100, self.energy + 0.003)

        else:

            self.energy = max(0, self.energy - 0.00025)

        if self.hunger < 20 or self.energy < 15:

            self.mood = max(0, self.mood - 0.00035)

        if self.mode == "happy" and self.frame >= self.wave_until:

            self.mode = "idle"

        if (self.desktop_visible and not self.sleeping and not self.dragging

                and self.frame >= self.next_cursor_wave

                and self.mode in ("idle", "walk")):

            pointer_x, pointer_y = self.root.winfo_pointerxy()

            pet_x = self.x + 150 * self.scale

            pet_y = self.y + 84 * self.scale

            if math.dist((pointer_x, pointer_y), (pet_x, pet_y)) <= PERSONALITIES[self.personality]["cursor_radius"] * self.scale:

                self.facing = 1 if pointer_x >= pet_x else -1

                self.mode = "happy"

                self.wave_until = self.frame + 60

                self.next_cursor_wave = self.frame + PERSONALITIES[self.personality]["cursor_cooldown"]

                self.say("hey there!")

        if (self.teleport_phase is not None
                and self.frame >= self.teleport_phase_until):
            if self.teleport_phase == "depart":
                self.x, self.y = self.teleport_target
                self.teleport_phase = "arrive"
                self.teleport_started_frame = self.frame
                self.teleport_phase_until = self.frame + 16
                self.mode = "teleport_arrive"
                self.route_history.append((round(self.x), round(self.y)))
                self.route_history = self.route_history[-14:]
                self.landing_frame = self.frame
            else:
                self.teleport_phase = None
                self.teleport_target = None
                self.teleport_from = None
                self.mode = "idle"
                self.next_hop_frame = self.frame + random.randint(
                    *PERSONALITIES[self.personality]["hop_wait"])
                self.next_crawl_frame = self.frame + PERSONALITIES[self.personality]["crawl_delay"]
                self.say("teleport complete!")
                self.save_state()

        if not self.dragging and not self.patrol_paused:

            if self.mode in ("teleport_charge", "teleport_arrive"):

                pass

            elif self.mode == "fall":

                self.vy += 0.7 * self.scale

                self.y = min(self.screen_h - self.height - 8, self.y + self.vy)

                if self.y >= self.screen_h - self.height - 8:

                    self.mode = "idle"

                    self.vy = 0

                    self.landing_frame = self.frame

            elif self.mode == "hop":

                self.advance_icon_hop()

            elif self.mode == "ceiling":

                self.y = 0

                self.x += (PERSONALITIES[self.personality]["surface_speed"] * self.scale
                            * self.facing * (1.7 if self.frame < self.zoomies_until else 1.0)
                            * self.movement_speed)

                if self.x <= 0 or self.x >= self.screen_w - self.width:

                    self.x = min(max(0, self.x), self.screen_w - self.width)

                    self.wall_side = "left" if self.x <= 0 else "right"

                    self.wall_direction = 1

                    self.mode = "wall"

            elif self.mode == "wall":

                self.x = 0 if self.wall_side == "left" else self.screen_w - self.width

                self.y += (PERSONALITIES[self.personality]["surface_speed"] * self.scale
                            * self.wall_direction * (1.7 if self.frame < self.zoomies_until else 1.0)
                            * self.movement_speed)

                wall_limit = self.screen_h * 0.42

                if self.wall_direction > 0 and self.y >= wall_limit:

                    self.y = wall_limit

                    self.wall_direction = -1

                elif self.wall_direction < 0 and self.y <= 0:

                    self.y = 0

                    self.facing = 1 if self.wall_side == "left" else -1

                    if self.frame >= self.ceiling_until:

                        self.mode = "idle"

                        self.next_hop_frame = self.frame

                    else:

                        self.mode = "ceiling"

            elif self.mode == "walk":

                delta = self.target_x - self.x

                if abs(delta) < 3:

                    self.mode = "idle"

                else:

                    self.facing = 1 if delta > 0 else -1

                    self.x += 2.2 * self.scale * self.movement_speed * self.facing

            elif self.desktop_visible and not self.sleeping and self.frame >= self.next_crawl_frame:

                self.begin_ceiling_crawl()

            elif self.icon_targets:

                if self.desktop_visible and not self.sleeping and self.frame >= self.next_hop_frame:

                    self.start_icon_hop()

            elif not self.sleeping and self.frame % 180 == 0:

                self.target_x = random.randint(0, max(0, self.screen_w - self.width))

                self.mode = "walk"

        if self.message_ticks > 0:

            self.message_ticks -= 1

        elif self.hunger < 18 and self.frame % 180 == 1:

            self.say("feed me, pls...")

        elif self.energy < 15 and self.frame % 180 == 1:

            self.say("need a recharge...")

        if self.focus_end and time.time() >= self.focus_end:

            self.focus_end = None

            self.say("focus complete! time for a break.")

            self.root.bell()

        if self.focus_end and time.time() >= self.focus_end:

            self.focus_end = None

            self.say("focus complete! time for a break.")

            self.root.bell()

        self.x = min(max(0, self.x), self.screen_w - self.width)

        self.move_window()

        self.draw()

        if self.frame % 100 == 0:

            self.save_state()

        self.root.after(TICK_MS, self.tick)

    def rect(self, x, y, w, h, color, tag="pet"):

        self.canvas.create_rectangle(x, y, x + w, y + h, fill=color,

                                     outline=color, tags=tag)

    def draw_companion(self):

        # Crisp blue terminal robot, inspired by the Codex desktop companion.

        c = self.canvas

        ox = 150

        bob = 2 if self.mode in ("walk", "play") and self.frame % 8 < 4 else 0

        oy = bob

        c.create_oval(91, 171 + oy, 209, 192 + oy, fill="#11182e", outline="")

        if self.level >= 2:

            c.create_arc(81, 43 + oy, 219, 185 + oy, start=35, extent=290,

                         style=tk.ARC, outline="#47a6f0", width=2)

        if self.level >= 3:

            c.create_polygon(108, 111 + oy, 79, 92 + oy, 88, 128 + oy,

                             112, 139 + oy, fill="#1d3aa6", outline="#6cc4ff", width=2)

            c.create_polygon(192, 111 + oy, 221, 92 + oy, 212, 128 + oy,

                             188, 139 + oy, fill="#1d3aa6", outline="#6cc4ff", width=2)

        # Boots, legs, side arms, and rounded blue body.

        c.create_line(127, 151 + oy, 121, 170 + oy, fill="#1f5fb4", width=12, capstyle=tk.ROUND)

        c.create_line(173, 151 + oy, 179, 170 + oy, fill="#1f5fb4", width=12, capstyle=tk.ROUND)

        c.create_oval(116, 153 + oy, 132, 168 + oy, fill="#6cc4ff", outline="#1f5fb4", width=2)

        c.create_oval(168, 153 + oy, 184, 168 + oy, fill="#6cc4ff", outline="#1f5fb4", width=2)

        c.create_oval(111, 164 + oy, 137, 178 + oy, fill="#1d3aa6", outline="#6cc4ff", width=2)

        c.create_oval(163, 164 + oy, 189, 178 + oy, fill="#1d3aa6", outline="#6cc4ff", width=2)

        c.create_line(119, 171 + oy, 129, 171 + oy, fill="#cfeaff", width=2)

        c.create_line(171, 171 + oy, 181, 171 + oy, fill="#cfeaff", width=2)

        c.create_line(104, 119 + oy, 91, 147 + oy, fill="#47a6f0", width=12, capstyle=tk.ROUND)

        c.create_line(196, 119 + oy, 209, 147 + oy, fill="#47a6f0", width=12, capstyle=tk.ROUND)

        c.create_line(100, 128 + oy, 94, 142 + oy, fill="#cfeaff", width=3, capstyle=tk.ROUND)

        c.create_line(200, 128 + oy, 206, 142 + oy, fill="#cfeaff", width=3, capstyle=tk.ROUND)

        c.create_oval(82, 140 + oy, 100, 158 + oy, fill="#c9d4ee", outline="#1f5fb4", width=3)

        c.create_oval(200, 140 + oy, 218, 158 + oy, fill="#c9d4ee", outline="#1f5fb4", width=3)

        c.create_oval(106, 116 + oy, 194, 174 + oy, fill="#3585d8", outline="#1f5fb4", width=4)

        c.create_arc(110, 118 + oy, 190, 167 + oy, start=25, extent=130,

                     style=tk.ARC, outline="#9bdcff", width=3)

        c.create_oval(117, 124 + oy, 183, 166 + oy, fill="#47a6f0", outline="#6cc4ff", width=2)

        c.create_polygon(130, 137 + oy, 150, 146 + oy, 170, 137 + oy,

                         165, 154 + oy, 135, 154 + oy,

                         fill="#cfeaff", outline="#1f5fb4", width=2)

        c.create_oval(143, 147 + oy, 157, 161 + oy, fill="#1d3aa6", outline="#c9d4ee", width=2)

        c.create_text(150, 154 + oy, text="✦", fill="#ffd34d" if self.level < 3 else WHITE,

                      font=("Consolas", 8, "bold"))

        c.create_line(122, 161 + oy, 135, 166 + oy, fill="#cfeaff", width=2)

        c.create_line(178, 161 + oy, 165, 166 + oy, fill="#cfeaff", width=2)

        # Monitor head, silver cap, and the familiar terminal prompt face.

        c.create_line(150, 52 + oy, 150, 42 + oy, fill="#c9d4ee", width=4)

        c.create_oval(144, 32 + oy, 156, 44 + oy, fill="#f3a6d8", outline="#eaf6ff", width=2)

        c.create_oval(98, 48 + oy, 202, 131 + oy, fill="#3585d8", outline="#1f5fb4", width=4)

        c.create_oval(105, 52 + oy, 195, 124 + oy, fill="#6cc4ff", outline="#cfeaff", width=2)

        c.create_arc(105, 52 + oy, 195, 121 + oy, start=25, extent=135,

                     style=tk.ARC, outline="#eaf6ff", width=3)

        c.create_rectangle(110, 69 + oy, 190, 115 + oy, fill="#1d3aa6", outline="#0f2a74", width=3)

        c.create_line(115, 73 + oy, 185, 73 + oy, fill="#47a6f0", width=2)

        for screw_x in (115, 185):

            c.create_oval(screw_x - 2, 74 + oy, screw_x + 2, 78 + oy,

                          fill="#c9d4ee", outline="")

        blink = not self.sleeping and self.frame % 145 < 4

        if self.sleeping or blink:

            c.create_line(119, 92 + oy, 130, 92 + oy, fill="#eaf6ff", width=3, capstyle=tk.ROUND)

        else:

            c.create_line(119, 84 + oy, 131, 92 + oy, 119, 100 + oy,

                          fill="#eaf6ff", width=4, capstyle=tk.ROUND, joinstyle=tk.ROUND)

        if self.sleeping or blink:

            c.create_line(143, 94 + oy, 166, 94 + oy, fill="#eaf6ff", width=4, capstyle=tk.ROUND)

        else:

            c.create_line(143, 100 + oy, 166, 100 + oy, fill="#eaf6ff", width=4, capstyle=tk.ROUND)

        c.create_oval(171, 88 + oy, 177, 94 + oy, fill="#f3a6d8", outline="")

        c.create_oval(101, 82 + oy, 109, 99 + oy, fill="#c9d4ee", outline="#1f5fb4", width=2)

        c.create_oval(191, 82 + oy, 199, 99 + oy, fill="#c9d4ee", outline="#1f5fb4", width=2)

        # Rounded cap gives the monitor its friendly robot silhouette.

        c.create_arc(112, 42 + oy, 188, 82 + oy, start=0, extent=180,

                     style=tk.PIESLICE, fill="#c9d4ee", outline="#1f5fb4", width=3)

        c.create_rectangle(112, 61 + oy, 188, 72 + oy, fill="#c9d4ee", outline="#1f5fb4", width=2)

        c.create_line(121, 63 + oy, 179, 63 + oy, fill="#47a6f0", width=3)

        c.create_oval(128, 49 + oy, 139, 54 + oy, fill="#eaf6ff", outline="")

        c.create_oval(161, 49 + oy, 172, 54 + oy, fill="#eaf6ff", outline="")

        if self.level >= 4:

            c.create_polygon(127, 53 + oy, 132, 38 + oy, 141, 52 + oy,

                             150, 34 + oy, 159, 52 + oy, 168, 38 + oy,

                             173, 53 + oy, fill="#ffd34d", outline="#1f5fb4", width=2)

    def draw_bar(self, x, y, label, value, color):

        c = self.canvas

        c.create_text(x, y, anchor="w", text=label, fill=color,

                      font=("Consolas", 8, "bold"), tags="hud")

        bx = x + 58

        c.create_rectangle(bx, y - 6, bx + 100, y + 4, fill="#11182e",

                           outline="#465274", tags="hud")

        fill = max(0, min(100, value))

        if fill:

            c.create_rectangle(bx + 1, y - 5, bx + 1 + 0.98 * fill, y + 3,

                               fill=color, outline=color, tags="hud")

    def draw(self):

        c = self.canvas

        c.delete("all")

        if self.pet_animations:

            pulse = (math.sin(self.frame * 0.12) + 1) / 2

            aura = GLOW_PALETTES.get(self.glow_theme, GLOW_PALETTES["Cyan"])
            if self.mood < 28:
                aura = PINK

            radius = 54 + pulse * 7

            c.create_oval(150 - radius, 84 - radius * 0.68,

                          150 + radius, 84 + radius * 0.68,

                          outline=aura, width=1 + int(pulse * 2), tags="aura")

            for spark in range(3):

                angle = self.frame * 0.045 + spark * (2 * math.pi / 3)

                orbit = radius + 8 * math.sin(self.frame * 0.08 + spark)

                sx = 150 + math.cos(angle) * orbit

                sy = 84 + math.sin(angle) * orbit * 0.68

                size = 2 + (spark == 0) * pulse

                c.create_oval(sx - size, sy - size, sx + size, sy + size,

                              fill=PINK if self.energy < 25 and spark == 0 else CYAN,

                              outline="", tags="aura")

        self.draw_teleport_effect()

        if self.pet_animations:

            if self.level >= 2:

                c.create_arc(72, 24, 228, 190, start=28, extent=300,

                             style=tk.ARC, outline="#47a6f0", width=3)

            if self.level >= 3:

                c.create_polygon(103, 123, 69, 101, 80, 143, 111, 151,

                                 fill="#1d3aa6", outline="#6cc4ff", width=2)

                c.create_polygon(197, 123, 231, 101, 220, 143, 189, 151,

                                 fill="#1d3aa6", outline="#6cc4ff", width=2)

            if self.mode == "wall":

                wall_pose = "wall_down" if self.wall_direction > 0 else "wall_up"

                animation = wall_pose if wall_pose in self.pet_animations else "right"

            elif self.mode in ("walk", "ceiling"):

                direction = "right" if self.facing > 0 else "left"

                animation = (f"ceiling_{direction}" if self.mode == "ceiling"

                             and f"ceiling_{direction}" in self.pet_animations else direction)

            elif self.mode == "happy":

                animation = "wave"

            elif self.mode in ("play", "hop", "teleport_charge", "teleport_arrive"):

                animation = "jump"

            else:

                animation = "idle"

            frames = self.pet_animations[animation]

            animation_step = (max(1, round(2 / self.movement_speed))
                              if self.mode in ("walk", "ceiling", "wall")
                              or self.frame < self.zoomies_until else
                              max(1, round(3 / self.movement_speed))
                              if self.mode in ("hop", "play") else 4)
            frame_index = (1 if self.sleeping else
                           (self.frame // animation_step) % len(frames))
            frame = frames[frame_index]
            pose_image = frame
            pose_scale_x = pose_scale_y = 1.0
            landing_age = self.frame - self.landing_frame
            if self.mode == "hop" and self.hop_duration > 0:
                hop_progress = min(1.0, max(0.0, self.hop_elapsed / self.hop_duration))
                stretch = math.sin(math.pi * hop_progress)
                pose_scale_x -= 0.08 * stretch
                pose_scale_y += 0.12 * stretch
            elif 0 <= landing_age < 5:
                squash = (5 - landing_age) / 5
                pose_scale_x += 0.18 * squash
                pose_scale_y -= 0.15 * squash

            if (Image is not None and ImageTk is not None
                    and animation in ("idle", "left", "right", "wave", "jump")
                    and (pose_scale_x != 1.0 or pose_scale_y != 1.0)):
                scale_x_key = max(1, round(pose_scale_x * 20))
                scale_y_key = max(1, round(pose_scale_y * 20))
                pose_key = (animation, frame_index, scale_x_key, scale_y_key)
                pose_image = self.sprite_pose_cache.get(pose_key)
                if pose_image is None:
                    sprite_path = (Path(__file__).resolve().parent / "assets" /
                                   f"codex_{animation}_{self.animation_scale_tag}_{frame_index}.png")
                    try:
                        with Image.open(sprite_path) as source_image:
                            source_image = source_image.convert("RGBA")
                            pose_size = (
                                max(1, round(source_image.width * scale_x_key / 20)),
                                max(1, round(source_image.height * scale_y_key / 20)))
                            resized = source_image.resize(pose_size, Image.NEAREST)
                        pose_image = ImageTk.PhotoImage(resized, master=self.root)
                        self.sprite_pose_cache[pose_key] = pose_image
                        if len(self.sprite_pose_cache) > 96:
                            self.sprite_pose_cache.pop(next(iter(self.sprite_pose_cache)))
                    except (OSError, tk.TclError, AttributeError):
                        pose_image = frame

            breathing = 1.4 * math.sin(self.frame * 0.10) if self.mode == "idle" else 0
            if pose_image is not frame:
                image_y = 84 + breathing + (frame.height() - pose_image.height()) / 2
            else:
                image_y = 84 + breathing

            if self.pet_animations and (self.mode in ("walk", "hop", "ceiling", "wall")
                                        or self.frame < self.zoomies_until):
                phase = (self.frame % 8) / 8
                if self.mode == "wall":
                    for index in range(3):
                        y = 48 + index * 20 + phase * 7 * self.wall_direction
                        c.create_line(132, y, 145, y - 7 * self.wall_direction,
                                      fill="#47a6f0", width=2, tags="motion")
                else:
                    for index in range(3):
                        y = 60 + index * 18
                        end_x = 150 - self.facing * (34 + index * 9)
                        start_x = end_x - self.facing * (12 + ((self.frame + index * 3) % 10))
                        c.create_line(start_x, y + phase * 2, end_x, y,
                                      fill=GLOW_PALETTES.get(self.glow_theme, CYAN)
                                      if index != 1 else PINK,
                                      width=2 if index == 1 else 1, tags="motion")

            tail_wave = math.sin(self.frame * 0.16) * 7
            tail_direction = -self.facing
            tail_root_x = 132 if self.facing > 0 else 168
            tail_points = (tail_root_x, 119,
                           tail_root_x + tail_direction * 13, 125 + tail_wave * 0.25,
                           tail_root_x + tail_direction * 27, 139 - tail_wave * 0.55,
                           tail_root_x + tail_direction * 38, 135 + tail_wave)
            c.create_line(*tail_points, smooth=True, splinesteps=16,
                          fill="#2847a2", width=10, capstyle=tk.ROUND, tags="pet-tail")
            c.create_line(*tail_points, smooth=True, splinesteps=16,
                          fill=GLOW_PALETTES.get(self.glow_theme, CYAN),
                          width=4, capstyle=tk.ROUND, tags="pet-tail")
            tail_tip_x, tail_tip_y = tail_points[-2:]
            c.create_oval(tail_tip_x - 4, tail_tip_y - 4,
                          tail_tip_x + 4, tail_tip_y + 4,
                          fill=PINK, outline=WHITE, width=1, tags="pet-tail")
            if (self.teleport_phase == "arrive" and self.teleport_from is not None
                    and self.teleport_target is not None):
                dx = self.teleport_target[0] - self.teleport_from[0]
                dy = self.teleport_target[1] - self.teleport_from[1]
                distance = max(1.0, math.hypot(dx, dy))
                progress = min(1.0, max(0.0,
                                (self.frame - self.teleport_started_frame) / 16))
                for index, offset in enumerate((18, 36)):
                    fade_steps = 5 if index == 0 else 3
                    opacity = max(0, int(round((1 - progress) * fade_steps)) * 32)
                    if opacity <= 0:
                        continue
                    echo = self.teleport_echo_image(frame_index, opacity)
                    echo_x = 150 - dx / distance * offset
                    echo_y = image_y - dy / distance * offset
                    if echo is not None:
                        c.create_image(echo_x, echo_y, image=echo,
                                       tags="teleport-afterimage")
                    else:
                        c.create_oval(echo_x - 5, echo_y - 5,
                                      echo_x + 5, echo_y + 5,
                                      fill=GLOW_PALETTES.get(self.glow_theme, CYAN),
                                      outline="", tags="teleport-afterimage")

            c.create_image(150, image_y, image=pose_image, tags="sprite")

            status = None
            status_color = CYAN
            if self.sleeping:
                status, status_color = "Zz", PURPLE
            elif self.hunger < 20:
                status, status_color = "!", PINK
            elif self.energy < 18:
                status, status_color = "⚡", "#ffd34d"
            elif self.mode == "happy":
                status, status_color = "♥", PINK
            if status:
                c.create_oval(204, 40, 232, 68, fill="#11182e",
                              outline=status_color, width=2, tags="mood")
                c.create_text(218, 54, text=status, fill=status_color,
                              font=("Segoe UI Symbol", 11, "bold"), tags="mood")

            if self.frame < self.affection_until:

                age = self.affection_until - self.frame

                c.create_text(210, 54 - (40 - age) * 0.7, text="♥",

                              fill=PINK, font=("Segoe UI Symbol", 23, "bold"),

                              tags="effect")

            if self.mode == "hop" and 0 <= self.hop_elapsed < 0.25:
                launch_radius = 7 + int(self.hop_elapsed * 42)
                c.create_oval(150 - launch_radius, 143 - launch_radius * 0.22,
                              150 + launch_radius, 143 + launch_radius * 0.22,
                              outline=PURPLE, width=2, tags="effect")

            landing_age = self.frame - self.landing_frame
            if 0 <= landing_age < 12:
                radius = 7 + landing_age * 3
                c.create_oval(150 - radius, 143 - radius * 0.24,
                              150 + radius, 143 + radius * 0.24,
                              outline=GLOW_PALETTES.get(self.glow_theme, CYAN),
                              width=max(1, 3 - landing_age // 4),
                              tags="effect")
                if landing_age < 5:
                    for spark in (-1, 1):
                        spark_x = 150 + spark * (18 + landing_age * 4)
                        spark_y = 142 - landing_age * 2
                        c.create_line(spark_x, spark_y, spark_x + spark * 5,
                                      spark_y - 5, fill=PINK, width=2,
                                      tags="effect")

            if self.level >= 4:

                c.create_polygon(128, 49, 135, 36, 143, 49, 150, 33,

                                 157, 49, 165, 36, 172, 49,

                                 fill="#ffd34d", outline="#1f5fb4", width=2)

        else:

            self.draw_companion()

        if self.icon_targets:

            target_number = ((self.icon_target_index + len(self.icon_targets) - 1)

                             % len(self.icon_targets) + 1)

            radar_left, radar_top = 92, 203

            radar_width, radar_height = 116, 58

            radar_right = radar_left + radar_width

            radar_bottom = radar_top + radar_height

            c.create_rectangle(radar_left, radar_top, radar_right, radar_bottom,

                               fill="#08111f", outline="#385272", width=1,

                               tags="tracker")

            c.create_line(radar_left, (radar_top + radar_bottom) / 2,

                          radar_right, (radar_top + radar_bottom) / 2,

                          fill="#1b2a42", tags="tracker")

            c.create_line((radar_left + radar_right) / 2, radar_top,

                          (radar_left + radar_right) / 2, radar_bottom,

                          fill="#1b2a42", tags="tracker")

            map_w = max(1, self.screen_w - self.width)

            map_h = max(1, self.screen_h - self.height)

            if not self.route_history:

                self.route_history.append((round(self.x), round(self.y)))

            route_points = list(self.route_history[-14:])

            if self.mode in ("hop", "ceiling", "wall"):

                route_points.append((self.x, self.y))

            trail = []

            for route_x, route_y in route_points:

                trail.extend((radar_left + 3 + (radar_width - 6) * route_x / map_w,

                              radar_top + 3 + (radar_height - 6) * route_y / map_h))

            if len(trail) >= 4:

                c.create_line(*trail, fill="#47a6f0", width=2,

                              dash=(2, 3), smooth=True, splinesteps=12,

                              tags="tracker")

            route_coords = []

            route_indices = [index for index in self.patrol_route

                             if 0 <= index < len(self.icon_targets)]

            for index in route_indices:

                route_x, route_y, _label = self.icon_targets[index]

                route_coords.extend((radar_left + 3 + (radar_width - 6) * route_x / map_w,

                                     radar_top + 3 + (radar_height - 6) * route_y / map_h))

            if len(route_coords) >= 4:

                route_coords.extend(route_coords[:2])

                c.create_line(*route_coords, fill="#9b67ff", width=2,

                              dash=(4, 3), smooth=True, splinesteps=12,

                              tags="tracker")

            for number, (icon_x, icon_y, _label) in enumerate(self.icon_targets):

                px = radar_left + 3 + (radar_width - 6) * icon_x / map_w

                py = radar_top + 3 + (radar_height - 6) * icon_y / map_h

                dot_color = "#ff4fd8" if number == (self.icon_target_index - 1) % len(self.icon_targets) else "#47a6f0" if number in self.patrol_route else "#263348"

                c.create_oval(px - 1.5, py - 1.5, px + 1.5, py + 1.5,

                              fill=dot_color, outline="", tags="tracker")

            if self.manual_destination == "HOME" and self.home_perch is not None:

                target_x, target_y = self.home_perch

                target_name = "HOME"

            else:

                target_x, target_y, target_name = self.icon_targets[(self.icon_target_index - 1) % len(self.icon_targets)]

            target_px = radar_left + 3 + (radar_width - 6) * target_x / map_w

            target_py = radar_top + 3 + (radar_height - 6) * target_y / map_h

            pet_px = radar_left + 3 + (radar_width - 6) * self.x / map_w

            pet_py = radar_top + 3 + (radar_height - 6) * self.y / map_h

            if self.mode == "hop":

                c.create_line(pet_px, pet_py, target_px, target_py,

                              fill="#ff4fd8", dash=(3, 3), width=2, tags="tracker")

            c.create_text(150, 266, text=f"DESTINATION: {target_name[:18]}",

                          fill="#8fa5c4", font=("Consolas", 7), tags="tracker")

            c.create_oval(pet_px - 3, pet_py - 3, pet_px + 3, pet_py + 3,

                          fill=CYAN, outline=WHITE, width=1, tags="tracker")

            state = "PAUSED" if self.patrol_paused else "WAVE" if self.mode == "happy" else "WALL" if self.mode == "wall" else "CEILING" if self.mode == "ceiling" else "CLIMB" if self.ceiling_pending else "HOP" if self.mode == "hop" else "ZOOM" if self.frame < self.zoomies_until else self.personality.upper()

            tracker = (f"{state} TO {target_name[:10]}  "

                       f"X:{int(self.x)} Y:{int(self.y)}  #{target_number}")

            c.create_rectangle(22, 273, 278, 301, fill="#08111f",

                               outline=CYAN, width=1, tags="tracker")

            c.create_text(150, 287, text=tracker, fill=CYAN,

                          font=("Consolas", 8, "bold"), tags="tracker")

            c.scale("all", 0, 0, self.scale, self.scale)

            return

        if self.message_ticks:

            c.create_rectangle(38, 3, 262, 31, fill="#11182e", outline=CYAN, width=1)

            c.create_text(150, 17, text=self.message[:30], fill=WHITE,

                          font=("Consolas", 14, "bold"))

        evolution = "SPARK" if self.level == 1 else "SCOUT" if self.level == 2 else "WING" if self.level == 3 else "CORE"

        c.create_text(150, 190, text=f"NEON  //  Lv {self.level} {evolution}", fill=CYAN,

                      font=("Consolas", 9, "bold"), tags="hud")

        xp_into_level = self.xp - 10 * (self.level - 1) ** 2

        xp_needed = 10 * self.level ** 2 - 10 * (self.level - 1) ** 2

        c.create_rectangle(116, 195, 184, 201, fill="#11182e", outline="#465274", tags="hud")

        c.create_rectangle(117, 196, 117 + 66 * xp_into_level / xp_needed, 200,

                           fill=CYAN, outline=CYAN, tags="hud")

        xp_into_level = self.xp - 10 * (self.level - 1) ** 2

        xp_needed = 10 * self.level ** 2 - 10 * (self.level - 1) ** 2

        c.create_rectangle(116, 195, 184, 201, fill="#11182e", outline="#465274", tags="hud")

        c.create_rectangle(117, 196, 117 + 66 * xp_into_level / xp_needed, 200,

                           fill=CYAN, outline=CYAN, tags="hud")

        self.draw_bar(50, 207, "FUEL", self.hunger, PINK)

        self.draw_bar(50, 223, "MOOD", self.mood, PURPLE)

        self.draw_bar(50, 239, "POWER", self.energy, CYAN)

        c.scale("all", 0, 0, self.scale, self.scale)

    def quit(self):

        self.save_state()

        self.root.destroy()

def package_version(code_text):

    tree = ast.parse(code_text)

    for node in tree.body:

        if isinstance(node, ast.Assign) and any(

                isinstance(target, ast.Name) and target.id == "APP_VERSION"

                for target in node.targets):

            value = ast.literal_eval(node.value)

            return value if isinstance(value, int) and not isinstance(value, bool) else 0

    return 0

def create_rollback_package(root, script_path):

    rollback = root / "neon.rollback.zip"

    temporary = root / ".neon.rollback.tmp"

    assets = root / "assets"

    try:

        with zipfile.ZipFile(temporary, "w", zipfile.ZIP_DEFLATED) as bundle:

            bundle.write(script_path, "neon_pet.py")

            if assets.is_dir():

                for path in assets.rglob("*"):

                    if path.is_file() and not path.is_symlink():

                        bundle.write(path, path.relative_to(root).as_posix())

        temporary.replace(rollback)

        return True

    except OSError:

        try:

            temporary.unlink(missing_ok=True)

        except OSError:

            pass

        return False

def restore_rollback_package(root):

    rollback = root / "neon.rollback.zip"

    try:

        with zipfile.ZipFile(rollback, "r") as bundle:

            if bundle.testzip() is not None:

                return False

            code_text = bundle.read("neon_pet.py").decode("utf-8")

            ast.parse(code_text)

            staged = []

            for item in bundle.infolist():

                if item.is_dir() or not item.filename.startswith("assets/"):

                    continue

                relative = PurePosixPath(item.filename)

                mode = (item.external_attr >> 16) & 0xFFFF

                if (len(relative.parts) != 2 or ".." in relative.parts

                        or not relative.name.startswith("codex_")

                        or relative.suffix.lower() not in (".png", ".webp")

                        or stat.S_ISLNK(mode) or item.file_size > 2_000_000):

                    return False

                data = bundle.read(item)

                if relative.suffix.lower() == ".png" and not data.startswith(b"\x89PNG\r\n\x1a\n"):

                    return False

                destination = root.joinpath(*relative.parts)

                destination.parent.mkdir(parents=True, exist_ok=True)

                temporary = destination.with_name(destination.name + ".rollback.tmp")

                temporary.write_bytes(data)

                staged.append((temporary, destination))

        code_temp = root / ".neon_pet.rollback.tmp"

        code_temp.write_text(code_text, encoding="utf-8")

        ast.parse(code_temp.read_text(encoding="utf-8"))

        for temporary, destination in staged:

            temporary.replace(destination)

        code_temp.replace(root / "neon_pet.py")

        return True

    except (OSError, ValueError, KeyError, UnicodeDecodeError, SyntaxError, zipfile.BadZipFile):

        return False

def apply_zip_update():

    """Apply a newer, syntax-valid app bundle from the user's local neon.zip."""

    root = Path(__file__).resolve().parent

    script_path = Path(__file__).resolve()

    package_path = root / "neon.zip"

    try:

        with zipfile.ZipFile(package_path, "r") as bundle:

            code_text = bundle.read("neon_pet.py").decode("utf-8")

            ast.parse(code_text)

            target_version = package_version(code_text)

            if target_version <= APP_VERSION:

                return False

            failed_version = root / ".neon_failed_update"

            try:

                if failed_version.read_text(encoding="utf-8").strip() == str(target_version):

                    return False

            except OSError:

                pass

            if bundle.testzip() is not None:

                return False

            asset_infos = []

            total_bytes = 0

            for item in bundle.infolist():

                if item.is_dir() or not item.filename.startswith("assets/"):

                    continue

                relative = PurePosixPath(item.filename)

                mode = (item.external_attr >> 16) & 0xFFFF

                if (len(relative.parts) != 2 or ".." in relative.parts

                        or not relative.name.startswith("codex_")

                        or relative.suffix.lower() not in (".png", ".webp")

                        or stat.S_ISLNK(mode) or item.file_size > 2_000_000):

                    return False

                total_bytes += item.file_size

                if total_bytes > 40_000_000:

                    return False

                asset_infos.append((item.filename, bundle.read(item)))

            names = {name for name, _data in asset_infos}

            required = {

                f"assets/codex_{animation}_{str(scale).replace('.', '_')}_{index}.png"

                for animation, count in (("idle", 6), ("right", 8), ("left", 8),

                                         ("wave", 4), ("jump", 5))

                for scale in (0.5, 0.75, 1.0, 1.5)

                for index in range(count)

            }

            if not required.issubset(names):

                return False

            for name, data in asset_infos:

                if name.lower().endswith(".png") and not data.startswith(b"\x89PNG\r\n\x1a\n"):

                    return False

    except (OSError, ValueError, KeyError, UnicodeDecodeError, SyntaxError, zipfile.BadZipFile):

        return False

    if not create_rollback_package(root, script_path):

        return False

    staged = []

    try:

        for name, data in asset_infos:

            destination = root.joinpath(*PurePosixPath(name).parts)

            destination.parent.mkdir(parents=True, exist_ok=True)

            temporary = destination.with_name(destination.name + ".update.tmp")

            temporary.write_bytes(data)

            staged.append((temporary, destination))

        code_temp = root / ".neon_pet.update.tmp"

        code_temp.write_text(code_text, encoding="utf-8")

        ast.parse(code_temp.read_text(encoding="utf-8"))

        for temporary, destination in staged:

            temporary.replace(destination)

        code_temp.replace(script_path)

    except (OSError, SyntaxError):

        for temporary, _destination in staged:

            try:

                temporary.unlink(missing_ok=True)

            except OSError:

                pass

        restore_rollback_package(root)

        return False

    ready_file = root / ".neon_update_ready"

    try:

        ready_file.unlink(missing_ok=True)

        flags = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)

        process = subprocess.Popen([sys.executable, str(script_path), "--neon-update-child"],

                                   cwd=str(root), stdin=subprocess.DEVNULL,

                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,

                                   creationflags=flags)

        deadline = time.monotonic() + 15

        while time.monotonic() < deadline:

            try:

                if ready_file.read_text(encoding="utf-8").strip() == str(target_version):

                    ready_file.unlink(missing_ok=True)

                    failed_version.unlink(missing_ok=True)

                    return True

            except OSError:

                pass

            if process.poll() is not None:

                break

            time.sleep(0.2)

        if process.poll() is None:

            process.terminate()

            try:

                process.wait(timeout=2)

            except subprocess.TimeoutExpired:

                process.kill()

        restore_rollback_package(root)

        failed_version.write_text(str(target_version), encoding="utf-8")

        return False

    except OSError:

        restore_rollback_package(root)

        try:

            failed_version.write_text(str(target_version), encoding="utf-8")

        except OSError:

            pass

        return False

def remember_startup_snapshot():

    """Keep a syntax-checked copy for the user's explicit repair-code command."""

    try:

        source_text = Path(__file__).resolve().read_text(encoding="utf-8")

        ast.parse(source_text)

        temporary = CODE_BACKUP_PATH.with_suffix(".tmp")

        temporary.write_text(source_text, encoding="utf-8")

        temporary.replace(CODE_BACKUP_PATH)

    except (OSError, SyntaxError):

        pass

def mark_update_ready():

    try:

        (Path(__file__).resolve().parent / ".neon_update_ready").write_text(

            str(APP_VERSION), encoding="utf-8")

    except OSError:

        pass

def enable_windows_dpi_awareness():

    if os.name != "nt":

        return

    try:

        import ctypes

        ctypes.windll.shcore.SetProcessDpiAwareness(2)

    except Exception:

        try:

            import ctypes

            ctypes.windll.user32.SetProcessDPIAware()

        except Exception:

            pass

if __name__ == "__main__":

    if apply_zip_update():

        raise SystemExit(0)

    remember_startup_snapshot()

    enable_windows_dpi_awareness()

    window = tk.Tk()

    Neon(window)

    if "--neon-update-child" in sys.argv[1:]:

        window.after(2000, mark_update_ready)

    window.mainloop()
