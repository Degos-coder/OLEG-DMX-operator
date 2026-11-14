"""OLEG DMX — an offline-first lighting console alpha for Windows.

The app uses only Python's standard UI toolkit. Install requirements.txt to
enable serial output to compatible USB-DMX interfaces.
"""

from __future__ import annotations

import copy
import colorsys
import json
import math
import os
import shutil
import tempfile
import threading
import time
import uuid
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk
import tkinter as tk

APP_VERSION = "Alpha 0.4"
APP_NAME = "OLEG"
DEFAULT_GROUPS = ["Передний план", "Сцена", "Задник"]
SLOT_SIZE = 16

BG = "#101319"
PANEL = "#191e27"
PANEL_2 = "#202733"
LINE = "#303947"
TEXT = "#edf2f7"
MUTED = "#9ba8b8"
ACCENT = "#61d9c3"
ACCENT_DARK = "#153e3a"
BLUE = "#86a9ff"
RED = "#ff687a"
YELLOW = "#e7bb69"


def uid() -> str:
    return uuid.uuid4().hex[:10]


def blank_look() -> dict:
    return {"dimmer": 0, "r": 0, "g": 0, "b": 0, "w": 0}


def default_show() -> dict:
    fixtures = []
    for i in range(6):
        fixtures.append({
            "id": f"par-{i + 1}",
            "name": f"PAR {i + 1:02d}",
            "address": 1 + i * SLOT_SIZE,
            "group": DEFAULT_GROUPS[i // 2],
            "offsets": {"r": 0, "g": 1, "b": 2, "w": 3},
            "look": blank_look(),
        })
    return {
        "format": "luma-dmx-show",
        "format_version": 1,
        "name": "Новое шоу",
        "groups": ["Все", *DEFAULT_GROUPS],
        "fixtures": fixtures,
        "scenes": [],
        "cues": [],
        "gangs": [],
        "stage": {"width_m": 8, "depth_m": 6, "objects": []},
    }


class DmxOutput:
    """Background serial sender using the ENTTEC DMX USB PRO packet format."""

    def __init__(self):
        self.port = None
        self.thread = None
        self.stop_event = threading.Event()
        self.lock = threading.Lock()
        self.frame = bytes(513)
        self.error = None

    @staticmethod
    def available_ports() -> list[str]:
        try:
            from serial.tools import list_ports
            return [port.device for port in list_ports.comports()]
        except Exception:
            return []

    def connect(self, port_name: str):
        try:
            import serial
        except ImportError as exc:
            raise RuntimeError("PySerial is missing. Install it with: pip install -r requirements.txt") from exc
        self.disconnect()
        try:
            self.port = serial.Serial(
                port=port_name,
                baudrate=250000,
                bytesize=serial.EIGHTBITS,
                parity=serial.PARITY_NONE,
                stopbits=serial.STOPBITS_TWO,
                timeout=0.1,
                write_timeout=0.2,
            )
        except Exception as exc:
            self.port = None
            raise RuntimeError(f"Could not open {port_name}: {exc}") from exc
        self.error = None
        self.stop_event.clear()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def _run(self):
        while not self.stop_event.is_set():
            with self.lock:
                payload = self.frame
            # ENTTEC USB DMX PRO: 0x7e, Send DMX label 6, length, start code + slots, 0xe7.
            length = len(payload)
            packet = bytes((0x7E, 6, length & 0xFF, (length >> 8) & 0xFF)) + payload + bytes((0xE7,))
            try:
                if self.port and self.port.is_open:
                    self.port.write(packet)
            except Exception as exc:
                self.error = str(exc)
                self.stop_event.set()
                break
            self.stop_event.wait(0.04)

    def send_frame(self, channels: bytes):
        with self.lock:
            self.frame = bytes((0,)) + channels[:512].ljust(512, b"\0")

    def disconnect(self):
        self.stop_event.set()
        if self.thread and self.thread.is_alive():
            self.thread.join(timeout=0.35)
        self.thread = None
        if self.port:
            try:
                self.port.close()
            except Exception:
                pass
        self.port = None

    @property
    def connected(self):
        return bool(self.port and self.port.is_open and not self.error)


class LumaApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title(f"{APP_NAME} · {APP_VERSION}")
        self.root.configure(bg=BG)
        self._preferences_path = self._get_preferences_path()
        self._ui_preferences = self._load_ui_preferences()
        self.auto_preview_next_var = tk.BooleanVar(value=bool(self._ui_preferences.get("auto_preview_next_after_fire", False)))
        self.saved_colors = self._load_saved_colors()
        try:
            self.root.geometry(self._ui_preferences.get("window_geometry", "1420x900"))
        except (tk.TclError, TypeError):
            self.root.geometry("1420x900")
        self.root.minsize(960, 680)
        self.show = default_show()
        self.file_path: Path | None = None
        self.output = DmxOutput()
        self.selected_ids: set[str] = {self.show["fixtures"][0]["id"]}
        self.group_filter = tk.StringVar(value="Все")
        self.fixture_sort_mode = tk.StringVar(value="Порядок")
        self.fade_var = tk.StringVar(value="1.0")
        self.fixture_sort_key = "order"
        self.fixture_sort_desc = False
        self.port_var = tk.StringVar()
        self.status_var = tk.StringVar(value="ОФЛАЙН-РЕЖИМ · шоу сохраняется локально")
        self.dirty = False
        self.faders: dict[str, tk.Scale] = {}
        self.fader_labels: dict[str, tk.Label] = {}
        self.slider_sync = False
        self.preview_canvas = None
        self.stage_canvases = []
        self.stage_selected_id = None
        self.stage_drag = None
        self.stage_edit_overlay = None
        self.preview_items = {}
        self.fixture_list = None
        self.patch_tree = None
        self.scene_tree = None
        self.cue_tree = None
        self._fade = None
        self.blackout_active = False
        self.gang_isolated_ids: set[str] = set()
        self._selection_sync = False
        self._undo_stack = []
        self._redo_stack = []
        self._history_interaction_snapshot = None
        self._app_clipboard = None
        self._context_kind = None
        self._mixed_fader_keys: set[str] = set()
        self._fixture_drag_id = None
        self._fixture_drag_ids = set()
        self._fixture_drag_start_y = 0
        self._fixture_drag_start_x = 0
        self._fixture_drag_active = False
        self._fixture_drop_index = None
        self.fixture_drop_indicator = None
        self.cue_edit_overlay = None
        self.hovered_cue_id = None
        self.space_preview_active = False
        self._gang_fader_previous = {key: 0 for key in ("dimmer", "r", "g", "b", "w")}
        self.preview_bounds = {}
        self.color_wheel_canvas = None
        self.color_wheel_image = None
        self.color_wheel_marker = None
        self.saved_colors_frame = None
        self._build_style()
        self._build_shell()
        self._bind_edit_shortcuts()
        self.root.after(400, self._restore_console_sashes)
        self._refresh_all()
        self._refresh_ports()
        self.root.protocol("WM_DELETE_WINDOW", self._close)
        self.root.after(33, self._tick)

    def _bind_edit_shortcuts(self):
        self.root.bind_all("<ButtonPress-1>", self._history_interaction_start, add="+")
        self.root.bind_all("<ButtonRelease-1>", self._history_interaction_finish, add="+")
        for sequence, operation in (("<Control-z>", self._undo), ("<Control-Shift-z>", self._redo),
                                     ("<Control-y>", self._redo), ("<Control-c>", self._copy_from_focus),
                                     ("<Control-x>", self._cut_from_focus), ("<Control-v>", self._paste_from_focus),
                                     ("<Delete>", self._delete_from_focus), ("<F2>", self._configure_from_focus),
                                     ("<Control-d>", self._duplicate_from_focus), ("<Control-s>", self._save_shortcut),
                                     ("<Control-n>", self._new_shortcut), ("<Control-o>", self._open_shortcut)):
            self.root.bind_all(sequence, operation, add="+")

    def _save_shortcut(self, _event=None):
        self.save_show()
        return "break"

    def _new_shortcut(self, _event=None):
        if self._editing_text_widget():
            return
        self.new_show()
        return "break"

    def _open_shortcut(self, _event=None):
        if self._editing_text_widget():
            return
        self.open_show()
        return "break"

    def _duplicate_from_focus(self, _event=None):
        if self._editing_text_widget():
            return
        kind = self._focused_context_kind()
        result = self._copy_context(kind)
        if result == "break":
            return self._paste_context(kind)
        return result

    def _history_interaction_start(self, _event=None):
        if getattr(_event, "widget", None) in (getattr(self, "undo_button", None), getattr(self, "redo_button", None)):
            return
        if self._history_interaction_snapshot is None:
            self._history_interaction_snapshot = copy.deepcopy(self.show)

    def _history_interaction_finish(self, _event=None):
        if self._history_interaction_snapshot is None:
            return
        before = self._history_interaction_snapshot
        self._history_interaction_snapshot = None
        self.root.after_idle(lambda state=before: self._push_undo_state(state))

    def _push_undo_state(self, state):
        if state == self.show:
            return
        if self._undo_stack and self._undo_stack[-1] == state:
            return
        self._undo_stack.append(copy.deepcopy(state))
        del self._undo_stack[:-100]
        self._redo_stack.clear()
        self._update_history_buttons()

    def _checkpoint_undo(self):
        state = copy.deepcopy(self.show)
        if self._undo_stack and self._undo_stack[-1] == state:
            return
        self._undo_stack.append(state)
        del self._undo_stack[:-100]
        self._redo_stack.clear()
        self._update_history_buttons()

    def _update_history_buttons(self):
        if getattr(self, "undo_button", None):
            self.undo_button.configure(state="normal" if self._undo_stack else "disabled")
        if getattr(self, "redo_button", None):
            self.redo_button.configure(state="normal" if self._redo_stack else "disabled")

    def _undo(self, _event=None):
        if self._editing_text_widget():
            return
        if not self._undo_stack:
            self.status_var.set("Нечего отменять")
            return "break"
        current_cue = getattr(self, "current_cue", -1)
        live_cue_id = self.show["cues"][current_cue]["id"] if 0 <= current_cue < len(self.show.get("cues", [])) else None
        self._redo_stack.append(copy.deepcopy(self.show))
        self.show = self._undo_stack.pop()
        self._update_history_buttons()
        self.dirty = True
        self._restore_after_history(live_cue_id)
        self.status_var.set("Изменение отменено · Ctrl+Shift+Z — повторить")
        return "break"

    def _redo(self, _event=None):
        if self._editing_text_widget():
            return
        if not self._redo_stack:
            self.status_var.set("Нечего повторять")
            return "break"
        current_cue = getattr(self, "current_cue", -1)
        live_cue_id = self.show["cues"][current_cue]["id"] if 0 <= current_cue < len(self.show.get("cues", [])) else None
        self._undo_stack.append(copy.deepcopy(self.show))
        self.show = self._redo_stack.pop()
        self._update_history_buttons()
        self.dirty = True
        self._restore_after_history(live_cue_id)
        self.status_var.set("Изменение повторено · Ctrl+Z — отменить")
        return "break"

    def _restore_after_history(self, live_cue_id=None):
        self._fade = None
        fixture_ids = {fixture.get("id") for fixture in self.show.get("fixtures", [])}
        self.selected_ids.intersection_update(fixture_ids)
        if not self.selected_ids and fixture_ids:
            self.selected_ids = {next(iter(fixture_ids))}
        stage_ids = {item.get("id") for item in self.show.get("stage", {}).get("objects", [])}
        if self.stage_selected_id not in stage_ids:
            self.stage_selected_id = None
        self.current_cue = next((index for index, cue in enumerate(self.show.get("cues", []))
                                 if cue.get("id") == live_cue_id), -1)
        self._refresh_all()

    def _editing_text_widget(self):
        widget = self.root.focus_get()
        return isinstance(widget, (tk.Entry, tk.Text, ttk.Entry, ttk.Combobox, tk.Spinbox))

    def _focused_context_kind(self):
        widget = self.root.focus_get()
        if widget in (self.stage_canvas, self.preview_canvas):
            return "fixture" if self._context_kind == "fixture" else "stage"
        if widget is self.cue_tree:
            return "cue"
        if widget is self.scene_tree:
            return "scene"
        if widget in (self.fixture_list, self.patch_tree):
            return "fixture"
        if widget is not None and widget is not self.root:
            return None
        return self._context_kind

    def _copy_from_focus(self, _event=None):
        if self._editing_text_widget():
            return
        return self._copy_context(self._focused_context_kind())

    def _cut_from_focus(self, _event=None):
        if self._editing_text_widget():
            return
        return self._copy_context(self._focused_context_kind(), cut=True)

    def _paste_from_focus(self, _event=None):
        if self._editing_text_widget():
            return
        return self._paste_context(self._focused_context_kind())

    def _delete_from_focus(self, _event=None):
        if self._editing_text_widget():
            return
        return self._delete_context(self._focused_context_kind())

    def _configure_from_focus(self, _event=None):
        if self._editing_text_widget():
            return
        return self._configure_context(self._focused_context_kind())

    def _copy_context(self, kind, cut=False):
        if kind == "stage":
            item = next((obj for obj in self._ensure_stage_objects() if obj.get("id") == self.stage_selected_id), None)
            if not item or item.get("kind") == "fixture":
                return
            self._app_clipboard = {"kind": "stage", "value": copy.deepcopy(item)}
            if cut:
                self._delete_stage_object()
        elif kind == "scene":
            item = self._selected_scene()
            if not item:
                return
            self._app_clipboard = {"kind": "scene", "value": copy.deepcopy(item)}
            if cut:
                self._checkpoint_undo()
                self.delete_selected_scene()
        elif kind == "cue":
            selection = self.cue_tree.selection() if self.cue_tree else ()
            items = [copy.deepcopy(cue) for cue in self.show.get("cues", []) if cue.get("id") in selection]
            if not items:
                return
            self._app_clipboard = {"kind": "cue", "value": items}
            if cut:
                self._checkpoint_undo()
                self.remove_cue()
        elif kind == "fixture":
            items = [copy.deepcopy(fixture) for fixture in self._selected_fixtures()]
            if not items:
                return
            self._app_clipboard = {"kind": "fixture", "value": items}
            if cut:
                self._checkpoint_undo()
                self._remove_selected_fixtures_from_show()
        else:
            return
        self.status_var.set("Скопировано" + (" и вырезано" if cut else "") + " · Ctrl+V — вставить")
        return "break"

    def _paste_context(self, kind):
        clip = self._app_clipboard
        if not clip or clip.get("kind") != kind:
            self.status_var.set("Буфер обмена не подходит для этого списка")
            return "break" if kind else None
        self._checkpoint_undo()
        if kind == "stage":
            item = copy.deepcopy(clip["value"])
            item["id"] = uid()
            item["x"] = min(.94, item.get("x", .5) + .04)
            item["y"] = min(.92, item.get("y", .5) + .04)
            self._ensure_stage_objects().append(item)
            self.stage_selected_id = item["id"]
            self.dirty = True
            self._draw_preview()
        elif kind == "scene":
            item = copy.deepcopy(clip["value"])
            item["id"] = uid()
            item["name"] = self._unique_copy_name(item.get("name", "Сцена"), [x.get("name") for x in self.show["scenes"]])
            self.show["scenes"].append(item)
            self.dirty = True
            self._refresh_scene_tree()
            self.scene_tree.selection_set(item["id"])
        elif kind == "cue":
            pasted = []
            for source in clip["value"]:
                item = copy.deepcopy(source)
                item["id"] = uid()
                item["label"] = self._unique_copy_name(item.get("label", "Snapshot"), [x.get("label") for x in self.show["cues"] + pasted])
                self.show["cues"].append(item)
                pasted.append(item)
            self.dirty = True
            self._refresh_cues()
            self.cue_tree.selection_set(*(item["id"] for item in pasted))
        elif kind == "fixture":
            inserted = []
            for source in clip["value"]:
                item = copy.deepcopy(source)
                item["id"] = uid()
                item["name"] = self._unique_copy_name(item.get("name", "PAR"), [x.get("name") for x in self.show["fixtures"] + inserted])
                item.pop("mirror_group_id", None)
                item["address"] = self._first_free_fixture_address(item, inserted)
                if item["address"] is None:
                    messagebox.showinfo("Патч", "Свободного участка адресов для копии прибора нет.", parent=self.root)
                    break
                inserted.append(item)
            self.show["fixtures"].extend(inserted)
            self.selected_ids = {item["id"] for item in inserted}
            self.dirty = bool(inserted) or self.dirty
            self._refresh_all()
        self.status_var.set("Вставлено из буфера обмена")
        return "break"

    @staticmethod
    def _unique_copy_name(name, existing):
        base = f"{name} — копия"
        candidate = base
        index = 2
        while candidate in existing:
            candidate = f"{base} {index}"
            index += 1
        return candidate

    def _first_free_fixture_address(self, fixture, additional=()):
        offsets = fixture.get("offsets", {"r": 0, "g": 1, "b": 2, "w": 3})
        used = {existing.get("address", 1) + offset
                for existing in [*self.show.get("fixtures", []), *additional]
                for offset in existing.get("offsets", {}).values()}
        footprint = max(offsets.values(), default=0) + 1
        for address in range(1, 513 - footprint + 1):
            channels = {address + offset for offset in offsets.values()}
            if not (channels & used):
                return address
        return None

    def _delete_context(self, kind):
        if kind == "stage":
            self._delete_stage_object()
        elif kind == "scene":
            self._checkpoint_undo()
            self.delete_selected_scene()
        elif kind == "cue":
            self._checkpoint_undo()
            self.remove_cue()
        elif kind == "fixture":
            self._checkpoint_undo()
            self._remove_selected_fixtures_from_show()
        else:
            return
        return "break"

    def _configure_context(self, kind):
        if kind == "stage":
            self._edit_stage_object()
        elif kind == "scene":
            self._edit_selected_scene()
        elif kind == "cue":
            self.edit_selected_cue()
        elif kind == "fixture":
            self.open_selected_patch_editor()
        else:
            return
        return "break"

    def _add_context_commands(self, menu, kind):
        menu.add_command(label="Настроить…", command=lambda: self._configure_context(kind))
        menu.add_command(label="Копировать", command=lambda: self._copy_context(kind))
        menu.add_command(label="Вырезать", command=lambda: self._copy_context(kind, cut=True))
        can_paste = bool(self._app_clipboard and self._app_clipboard.get("kind") == kind)
        menu.add_command(label="Вставить", command=lambda: self._paste_context(kind), state="normal" if can_paste else "disabled")
        menu.add_command(label="Удалить", command=lambda: self._delete_context(kind))

    def _edit_selected_scene(self):
        scene = self._selected_scene()
        if not scene:
            return
        name = simpledialog.askstring("Настроить сцену", "Название сцены:", initialvalue=scene.get("name", "Сцена"), parent=self.root)
        if name is None:
            return
        self._checkpoint_undo()
        scene["name"] = name.strip() or scene.get("name", "Сцена")
        self.dirty = True
        self._refresh_scene_tree()
        self.scene_tree.selection_set(scene["id"])

    def _remove_selected_fixtures_from_show(self):
        ids = set(self.selected_ids)
        if not ids:
            return
        self.show["fixtures"] = [fixture for fixture in self.show.get("fixtures", []) if fixture.get("id") not in ids]
        stage = self.show.setdefault("stage", {"objects": []})
        stage["objects"] = [item for item in stage.get("objects", []) if item.get("fixture_id") not in ids]
        for scene in self.show.get("scenes", []):
            for fixture_id in ids:
                scene.get("look", {}).pop(fixture_id, None)
        for cue in self.show.get("cues", []):
            cue["update_fixtures"] = [fixture_id for fixture_id in cue.get("update_fixtures", []) if fixture_id not in ids]
            for fixture_id in ids:
                cue.get("look", {}).pop(fixture_id, None)
        for gang in self.show.get("gangs", []):
            gang["members"] = [member for member in gang.get("members", []) if member not in ids]
        self.selected_ids.clear()
        self.dirty = True
        self._refresh_all()

    @staticmethod
    def _get_preferences_path():
        base = Path(os.environ.get("APPDATA", Path.home()))
        return base / "LUMA DMX" / "preferences.json"

    def _load_ui_preferences(self):
        try:
            with self._preferences_path.open("r", encoding="utf-8") as stream:
                preferences = json.load(stream)
            return preferences if isinstance(preferences, dict) else {}
        except (OSError, ValueError, TypeError):
            return {}

    def _load_saved_colors(self):
        result = []
        items = self._ui_preferences.get("saved_colors", [])
        if not isinstance(items, list):
            return result
        for item in items:
            if not isinstance(item, dict) or not isinstance(item.get("name"), str):
                continue
            values = item.get("rgbw")
            if (isinstance(values, dict) and all(isinstance(values.get(key), int) and 0 <= values[key] <= 255
                                                for key in ("r", "g", "b", "w"))):
                result.append({"name": item["name"], "rgbw": {key: values[key] for key in ("r", "g", "b", "w")}})
        return result

    def _save_ui_preferences(self):
        if not hasattr(self, "console_panes"):
            return
        preferences = dict(self._ui_preferences)
        preferences["saved_colors"] = self.saved_colors
        preferences["auto_preview_next_after_fire"] = bool(self.auto_preview_next_var.get())
        preferences["window_geometry"] = self.root.winfo_geometry()
        try:
            width = max(1, self.console_panes.winfo_width())
            height = max(1, self.center_panes.winfo_height())
            preferences["console_sashes"] = [self.console_panes.sashpos(i) / width for i in range(2)]
            preferences["center_sash"] = self.center_panes.sashpos(0) / height
            self._preferences_path.parent.mkdir(parents=True, exist_ok=True)
            temporary = self._preferences_path.with_suffix(".tmp")
            with temporary.open("w", encoding="utf-8") as stream:
                json.dump(preferences, stream, ensure_ascii=False, indent=2)
            os.replace(temporary, self._preferences_path)
            self._ui_preferences = preferences
        except (OSError, tk.TclError, ZeroDivisionError):
            pass

    def _schedule_preferences_save(self, _event=None):
        after_id = getattr(self, "_preferences_save_after", None)
        if after_id:
            self.root.after_cancel(after_id)
        self._preferences_save_after = self.root.after(250, self._save_ui_preferences)

    def _restore_console_sashes(self):
        try:
            ratios = self._ui_preferences.get("console_sashes", [])
            width = self.console_panes.winfo_width()
            height = self.center_panes.winfo_height()
            if width > 1 and len(ratios) == 2:
                for index, ratio in enumerate(ratios):
                    self.console_panes.sashpos(index, max(180, min(width - 180, round(width * float(ratio)))))
            ratio = float(self._ui_preferences.get("center_sash", 0.78))
            if height > 1:
                self.center_panes.sashpos(0, max(180, min(height - 120, round(height * ratio))))
        except (tk.TclError, TypeError, ValueError):
            pass

    def _build_style(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TFrame", background=BG)
        style.configure("Panel.TFrame", background=PANEL)
        style.configure("TLabel", background=BG, foreground=TEXT, font=("Segoe UI", 10))
        style.configure("Muted.TLabel", background=BG, foreground=MUTED, font=("Segoe UI", 9))
        style.configure("Panel.TLabel", background=PANEL, foreground=TEXT, font=("Segoe UI", 10))
        style.configure("PanelMuted.TLabel", background=PANEL, foreground=MUTED, font=("Segoe UI", 9))
        style.configure("Title.TLabel", background=BG, foreground=TEXT, font=("Segoe UI Semibold", 18))
        style.configure("Section.TLabel", background=PANEL, foreground=TEXT, font=("Segoe UI Semibold", 10))
        style.configure("TNotebook", background=BG, borderwidth=0)
        style.configure("TNotebook.Tab", background=PANEL, foreground=MUTED, padding=(18, 10), borderwidth=0)
        style.map("TNotebook.Tab", background=[("selected", ACCENT_DARK)], foreground=[("selected", ACCENT)])
        style.configure("Treeview", background=PANEL, fieldbackground=PANEL, foreground=TEXT,
                        rowheight=30, borderwidth=0, font=("Segoe UI", 9))
        style.configure("Treeview.Heading", background=PANEL_2, foreground=MUTED,
                        relief="flat", font=("Segoe UI Semibold", 9))
        style.map("Treeview", background=[("selected", "#244b52")], foreground=[("selected", TEXT)])
        style.configure("TCombobox", fieldbackground=PANEL_2, background=PANEL_2, foreground=TEXT, arrowcolor=TEXT)
        style.map("TCombobox", fieldbackground=[("readonly", PANEL_2)], foreground=[("readonly", TEXT)])

    def _button(self, parent, text, command, primary=False, small=False, width=None):
        bg = ACCENT_DARK if primary else PANEL_2
        fg = ACCENT if primary else TEXT
        btn = tk.Button(parent, text=text, command=command, bg=bg, fg=fg,
                        activebackground="#285b55" if primary else "#303b49", activeforeground=TEXT,
                        relief="flat", bd=0, padx=12 if not small else 9, pady=8 if not small else 5,
                        font=("Segoe UI Semibold", 9 if small else 10), cursor="hand2", width=width)
        return btn

    def _build_shell(self):
        header = tk.Frame(self.root, bg=BG, padx=20, pady=12)
        header.pack(fill="x")
        brand = tk.Frame(header, bg=BG)
        brand.pack(side="left")
        tk.Label(brand, text="OLEG", fg=ACCENT, bg=BG, font=("Segoe UI Black", 21)).pack(side="left")
        tk.Label(brand, text=f"  DMX   /   {APP_VERSION.upper()}", fg=MUTED, bg=BG, font=("Segoe UI Semibold", 9)).pack(side="left", pady=(6, 0))
        self.show_title = tk.Label(header, text=self.show["name"], fg=TEXT, bg=BG,
                                   font=("Segoe UI Semibold", 12))
        self.show_title.pack(side="left", padx=28)
        tools = tk.Frame(header, bg=BG)
        tools.pack(side="right")
        self._button(tools, "Новое шоу", self.new_show, small=True).pack(side="left", padx=3)
        self._button(tools, "Открыть", self.open_show, small=True).pack(side="left", padx=3)
        self._button(tools, "Сохранить", self.save_show, primary=True, small=True).pack(side="left", padx=(3, 14))
        self.port_combo = ttk.Combobox(tools, textvariable=self.port_var, width=12, state="normal")
        self.port_combo.pack(side="left", padx=4, ipady=5)
        self._button(tools, "↻", self._refresh_ports, small=True).pack(side="left", padx=2)
        self.connect_button = self._button(tools, "Подключить DMX", self.toggle_dmx, small=True)
        self.connect_button.pack(side="left", padx=4)
        tk.Frame(self.root, bg=LINE, height=1).pack(fill="x")

        status = tk.Frame(self.root, bg="#151a21", padx=20, pady=6)
        status.pack(fill="x")
        self.status_dot = tk.Label(status, text="●", fg=YELLOW, bg="#151a21", font=("Segoe UI", 9))
        self.status_dot.pack(side="left")
        tk.Label(status, textvariable=self.status_var, fg=MUTED, bg="#151a21",
                 font=("Segoe UI", 9)).pack(side="left", padx=8)
        tk.Label(status, text="1 ВСЕЛЕННАЯ  ·  512 КАНАЛОВ  ·  ГОТОВО К РАБОТЕ ОФЛАЙН", fg="#718093", bg="#151a21",
                 font=("Segoe UI Semibold", 8)).pack(side="right")

        self.tabs = ttk.Notebook(self.root)
        self.tabs.pack(fill="both", expand=True, padx=14, pady=(12, 8))
        self.live_tab = tk.Frame(self.tabs, bg=BG)
        self.patch_tab = tk.Frame(self.tabs, bg=BG)
        self.cue_tab = tk.Frame(self.tabs, bg=BG)
        self.stage_tab = tk.Frame(self.tabs, bg=BG)
        self.tabs.add(self.live_tab, text="ПУЛЬТ")
        self.tabs.add(self.patch_tab, text="ПАТЧ")
        self.tabs.add(self.cue_tab, text="SNAPSHOTS")
        self.tabs.add(self.stage_tab, text="СЦЕНА")
        self._build_live()
        self._build_patch()
        self._build_cues()
        self._build_stage_tab()
        self._build_gangs()
        footer = tk.Frame(self.root, bg=BG, padx=18, pady=5)
        footer.pack(fill="x")
        tk.Label(footer, text=f"{APP_VERSION}  ·  Локальное шоу  ·  Офлайн-режим",
                 fg="#6f7c8c", bg=BG, font=("Segoe UI", 8)).pack(side="left")
        self.blackout_button = self._button(footer, "ЗАТЕМНЕНИЕ", self.blackout, small=True)
        self.blackout_button.pack(side="right", padx=(8, 4))
        history = tk.Frame(footer, bg=BG)
        history.pack(side="right")
        self.undo_button = self._button(history, "↶ Отменить", self._undo, small=True)
        self.undo_button.pack(side="left", padx=3)
        self.redo_button = self._button(history, "↷ Повторить", self._redo, small=True)
        self.redo_button.pack(side="left", padx=3)
        self._update_history_buttons()

    def _panel(self, parent, title, subtitle=None):
        frame = tk.Frame(parent, bg=PANEL, highlightthickness=1, highlightbackground=LINE)
        head = tk.Frame(frame, bg=PANEL, padx=14, pady=12)
        head.pack(fill="x")
        tk.Label(head, text=title, bg=PANEL, fg=TEXT, font=("Segoe UI Semibold", 10)).pack(anchor="w")
        if subtitle:
            tk.Label(head, text=subtitle, bg=PANEL, fg=MUTED, font=("Segoe UI", 8)).pack(anchor="w", pady=(3, 0))
        return frame

    def _build_live(self):
        self.console_panes = ttk.Panedwindow(self.live_tab, orient="horizontal")
        self.console_panes.pack(fill="both", expand=True)
        self.console_panes.bind("<ButtonRelease-1>", self._schedule_preferences_save, add="+")
        left = self._panel(self.console_panes, "ПРИБОРЫ", "Выберите один или несколько приборов для настройки")
        self.console_panes.add(left, weight=2)
        group_row = tk.Frame(left, bg=PANEL, padx=10)
        group_row.pack(fill="x")
        tk.Label(group_row, text="ГРУППА", fg=MUTED, bg=PANEL, font=("Segoe UI Semibold", 8)).pack(anchor="w")
        self.group_combo = ttk.Combobox(group_row, textvariable=self.group_filter, state="readonly")
        self.group_combo.pack(fill="x", pady=(5, 8))
        self.group_combo.bind("<<ComboboxSelected>>", lambda _e: self._refresh_fixture_list())
        tk.Label(group_row, text="СОРТИРОВКА", fg=MUTED, bg=PANEL, font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(2, 0))
        self.fixture_sort_combo = ttk.Combobox(group_row, textvariable=self.fixture_sort_mode, state="readonly",
                                               values=("Порядок", "Имя", "Адрес", "Группа"))
        self.fixture_sort_combo.pack(fill="x", pady=(4, 7))
        self.fixture_sort_combo.bind("<<ComboboxSelected>>", lambda _e: self._set_fixture_sort(self.fixture_sort_mode.get()))
        self.fixture_list = tk.Listbox(left, selectmode="extended", bg=PANEL, fg=TEXT,
                                       selectbackground="#244b52", selectforeground=TEXT,
                                       highlightthickness=0, bd=0, activestyle="none",
                                       font=("Segoe UI", 10), height=13)
        self.fixture_list.pack(fill="both", expand=True, padx=10, pady=4)
        self.fixture_list.bind("<<ListboxSelect>>", self._on_fixture_select)
        self.fixture_list.bind("<ButtonPress-1>", self._fixture_drag_start)
        self.fixture_list.bind("<B1-Motion>", self._fixture_drag_motion)
        self.fixture_list.bind("<ButtonRelease-1>", self._fixture_drag_release)
        self.fixture_list.bind("<Button-3>", self._fixture_context_menu)
        self.fixture_drop_indicator = tk.Frame(self.fixture_list, bg=ACCENT, height=3)
        assign = tk.Frame(left, bg=PANEL, padx=10, pady=8)
        assign.pack(fill="x")
        self.assign_group = ttk.Combobox(assign, state="normal")
        self.assign_group.pack(fill="x", pady=(0, 6))
        self._button(assign, "Назначить в группу", self.assign_selected_group, small=True).pack(fill="x")
        self._button(assign, "Изменить выбранный прибор…", self.open_selected_patch_editor, small=True).pack(fill="x", pady=(5, 0))

        center = tk.Frame(self.console_panes, bg=BG)
        self.console_panes.add(center, weight=6)
        self.center_panes = ttk.Panedwindow(center, orient="vertical")
        self.center_panes.pack(fill="both", expand=True, padx=4, pady=(0, 8))
        self.center_panes.bind("<ButtonRelease-1>", self._schedule_preferences_save, add="+")
        stage = self._panel(self.center_panes, "ВИЗУАЛИЗАЦИЯ СЦЕНЫ", "Щёлкните по прибору, чтобы выбрать его · без DMX показывается симуляция")
        self.center_panes.add(stage, weight=6)
        stage_toolbar = tk.Frame(stage, bg=PANEL, padx=10, pady=0)
        stage_toolbar.pack(fill="x")
        self.live_snapshot_label = tk.Label(stage_toolbar, text="LIVE · SNAPSHOT НЕ ВЫЗВАН", bg=PANEL, fg=ACCENT,
                                            font=("Segoe UI Semibold", 8), anchor="w")
        self.live_snapshot_label.pack(side="left")
        self._button(stage_toolbar, "↗ Открыть вкладку сцены", self.open_stage_editor, primary=True, small=True).pack(side="right")
        self.preview_canvas = tk.Canvas(stage, bg="#111820", highlightthickness=0, height=380)
        self.preview_canvas.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        self.preview_canvas.bind("<Configure>", lambda _e: self._draw_preview())
        self.preview_canvas.bind("<Button-1>", self._on_preview_click)
        self.preview_canvas.bind("<Button-3>", self._stage_context_menu)
        self.stage_canvases.append((self.preview_canvas, False))
        self.live_tools_tabs = ttk.Notebook(self.center_panes)
        self.center_panes.add(self.live_tools_tabs, weight=2)
        scene_panel = tk.Frame(self.live_tools_tabs, bg=PANEL)
        self.gang_panel = tk.Frame(self.live_tools_tabs, bg=PANEL)
        self.live_tools_tabs.add(scene_panel, text="СЦЕНЫ")
        self.live_tools_tabs.add(self.gang_panel, text="GANGS")
        scene_tools = tk.Frame(scene_panel, bg=PANEL, padx=10, pady=3)
        scene_tools.pack(fill="x")
        self._button(scene_tools, "＋ Сохранить состояние", self.store_scene, primary=True, small=True).pack(side="left")
        self._button(scene_tools, "＋ Сцена и snapshot", self.store_scene_and_cue, small=True).pack(side="left", padx=5)
        self._button(scene_tools, "В snapshots", self.add_selected_scene_to_cue, small=True).pack(side="left")
        tk.Label(scene_tools, text="ПЕРЕХОД СЕК.", bg=PANEL, fg=MUTED, font=("Segoe UI Semibold", 8)).pack(side="left", padx=(12, 4))
        tk.Entry(scene_tools, textvariable=self.fade_var, width=5, bg=PANEL_2, fg=TEXT,
                 insertbackground=TEXT, relief="flat", justify="center").pack(side="left", ipady=3)
        self._button(scene_tools, "Вызвать", self.recall_selected_scene, small=True).pack(side="left", padx=5)
        self._button(scene_tools, "Удалить", self.delete_selected_scene, small=True).pack(side="left")
        self.scene_tree = ttk.Treeview(scene_panel, columns=("name", "fixtures"), show="headings", height=4, selectmode="browse")
        self.scene_tree.heading("name", text="СЦЕНА")
        self.scene_tree.heading("fixtures", text="ПРИБОРОВ")
        self.scene_tree.column("name", width=240)
        self.scene_tree.column("fixtures", width=110, anchor="center")
        self.scene_tree.pack(fill="x", padx=10, pady=(2, 10))
        self.scene_tree.bind("<Double-1>", lambda _e: self.recall_selected_scene())
        self.scene_tree.bind("<Button-3>", self._scene_context_menu)

        right = self._panel(self.console_panes, "ПРОГРАММАТОР", "Текущие значения выбранных приборов")
        self.console_panes.add(right, weight=3)
        self.selection_label = tk.Label(right, text="PAR 01", bg=PANEL, fg=ACCENT,
                                        font=("Segoe UI Semibold", 10), padx=14, pady=2)
        self.selection_label.pack(anchor="w")
        self._make_fader(right, "ЯРКОСТЬ", "dimmer", "#f1f4f7")
        self._make_fader(right, "КРАСНЫЙ", "r", "#ff6675")
        self._make_fader(right, "ЗЕЛЁНЫЙ", "g", "#53d69a")
        self._make_fader(right, "СИНИЙ", "b", "#6494ff")
        self._make_fader(right, "БЕЛЫЙ", "w", "#edf2f7")
        wheel_panel = tk.Frame(right, bg=PANEL, padx=14, pady=8)
        wheel_panel.pack(fill="x")
        tk.Label(wheel_panel, text="ЦВЕТОВОЕ КОЛЕСО RGBW", fg=MUTED, bg=PANEL,
                 font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(0, 5))
        self.color_wheel_canvas = tk.Canvas(wheel_panel, width=190, height=190, bg=PANEL,
                                            highlightthickness=0, cursor="crosshair")
        self.color_wheel_canvas.pack(anchor="center")
        self.color_wheel_canvas.bind("<Button-1>", self._color_wheel_pick)
        self.color_wheel_canvas.bind("<B1-Motion>", self._color_wheel_pick)
        self.color_wheel_canvas.bind("<ButtonPress-1>", self._history_interaction_start, add="+")
        self._draw_color_wheel()
        palette_panel = tk.Frame(right, bg=PANEL, padx=14, pady=8)
        palette_panel.pack(fill="x")
        palette_header = tk.Frame(palette_panel, bg=PANEL)
        palette_header.pack(fill="x")
        tk.Label(palette_header, text="СОХРАНЁННЫЕ ЦВЕТА", fg=MUTED, bg=PANEL,
                 font=("Segoe UI Semibold", 8)).pack(side="left")
        self._button(palette_header, "＋ Сохранить", self.save_current_color, small=True).pack(side="right")
        self.saved_colors_frame = tk.Frame(palette_panel, bg=PANEL)
        self.saved_colors_frame.pack(fill="x", pady=(6, 0))
        self._refresh_saved_colors()

    def _make_fader(self, parent, title, key, color):
        shell = tk.Frame(parent, bg=PANEL, padx=14, pady=6)
        shell.pack(fill="x")
        header = tk.Frame(shell, bg=PANEL)
        header.pack(fill="x")
        tk.Label(header, text=title, fg=MUTED, bg=PANEL, font=("Segoe UI Semibold", 8)).pack(side="left")
        val = tk.Label(header, text="0", fg=TEXT, bg=PANEL, font=("Consolas", 10, "bold"))
        val.pack(side="right")
        scale = tk.Scale(shell, from_=0, to=255, orient="horizontal", showvalue=0, resolution=1,
                         bg=PANEL, fg=TEXT, troughcolor=PANEL_2, activebackground=color,
                         highlightthickness=0, bd=0, sliderrelief="flat", length=220,
                         command=lambda value, k=key: self._on_fader(k, int(float(value))))
        scale.pack(fill="x")
        scale.bind("<ButtonPress-1>", self._history_interaction_start, add="+")
        self.faders[key] = scale
        self.fader_labels[key] = val

    def _draw_color_wheel(self):
        if not self.color_wheel_canvas:
            return
        size = 190
        center = (size - 1) / 2
        radius = 88
        image = tk.PhotoImage(width=size, height=size)
        for y in range(size):
            row = []
            for x in range(size):
                dx, dy = x - center, center - y
                distance = math.hypot(dx, dy)
                if distance > radius:
                    row.append(PANEL)
                    continue
                hue = (math.atan2(dy, dx) / (2 * math.pi)) % 1
                saturation = min(1, distance / radius)
                red, green, blue = colorsys.hsv_to_rgb(hue, saturation, 1)
                row.append("#%02x%02x%02x" % (round(red * 255), round(green * 255), round(blue * 255)))
            image.put("{" + " ".join(row) + "}", to=(0, y))
        self.color_wheel_image = image
        self.color_wheel_canvas.delete("all")
        self.color_wheel_canvas.create_image(size // 2, size // 2, image=image, tags=("wheel",))
        self._update_color_wheel_marker()

    def _update_color_wheel_marker(self):
        if not self.color_wheel_canvas or not self.color_wheel_image:
            return
        selected = self._selected_fixtures()
        look = selected[0]["look"] if selected else blank_look()
        white = look.get("w", 0) / 255 * 0.72
        rgb = [min(1, look.get(key, 0) / 255 + white) for key in ("r", "g", "b")]
        hue, saturation, _value = colorsys.rgb_to_hsv(*rgb)
        center, radius = 94.5, 88
        angle = hue * 2 * math.pi
        x = center + math.cos(angle) * saturation * radius
        y = center - math.sin(angle) * saturation * radius
        self.color_wheel_canvas.delete("marker")
        self.color_wheel_canvas.create_oval(x - 7, y - 7, x + 7, y + 7,
                                            outline="#111820", width=3, tags=("marker",))
        self.color_wheel_canvas.create_oval(x - 6, y - 6, x + 6, y + 6,
                                            outline="#ffffff", width=1, tags=("marker",))

    def _color_wheel_pick(self, event):
        selected = self._selected_fixtures()
        if not selected:
            return "break"
        if event.type == tk.EventType.ButtonPress and self._history_interaction_snapshot is None:
            self._history_interaction_snapshot = copy.deepcopy(self.show)
        center, radius = 94.5, 88
        dx, dy = event.x - center, center - event.y
        distance = math.hypot(dx, dy)
        if distance > radius:
            return "break"
        hue = (math.atan2(dy, dx) / (2 * math.pi)) % 1
        saturation = min(1, distance / radius)
        rgb = tuple(round(value * 255) for value in colorsys.hsv_to_rgb(hue, saturation, 1))
        white = min(rgb)
        self._apply_rgbw_color({"r": rgb[0] - white, "g": rgb[1] - white,
                                "b": rgb[2] - white, "w": white})
        return "break"

    def _refresh_saved_colors(self):
        if not self.saved_colors_frame:
            return
        for child in self.saved_colors_frame.winfo_children():
            child.destroy()
        if not self.saved_colors:
            tk.Label(self.saved_colors_frame, text="Пока нет сохранённых цветов", bg=PANEL, fg=MUTED,
                     font=("Segoe UI", 8)).pack(anchor="w", pady=4)
            return
        for index, saved in enumerate(self.saved_colors):
            values = saved["rgbw"]
            white = round(values["w"] * 0.72)
            swatch = "#%02x%02x%02x" % tuple(min(255, values[key] + white) for key in ("r", "g", "b"))
            chip = tk.Frame(self.saved_colors_frame, bg=PANEL)
            chip.grid(row=index // 3, column=index % 3, sticky="ew", padx=(0, 5), pady=3)
            self.saved_colors_frame.grid_columnconfigure(index % 3, weight=1)
            button = tk.Button(chip, text="", bg=swatch, activebackground=swatch, relief="flat", bd=0,
                               height=1, cursor="hand2", command=lambda i=index: self.apply_saved_color(i))
            button.pack(fill="x")
            button.bind("<Button-3>", lambda _event, i=index: self.remove_saved_color(i))
            tk.Label(chip, text=saved["name"][:12], bg=PANEL, fg=TEXT,
                     font=("Segoe UI", 8)).pack(fill="x")

    def save_current_color(self):
        selected = self._selected_fixtures()
        if not selected:
            messagebox.showinfo("Цвет", "Сначала выберите прибор в пульте.")
            return
        initial_name = f"Цвет {len(self.saved_colors) + 1}"
        name = simpledialog.askstring("Сохранить цвет", "Название цвета:", initialvalue=initial_name, parent=self.root)
        if not name or not name.strip():
            return
        look = selected[0]["look"]
        saved = {"name": name.strip(), "rgbw": {key: round(look.get(key, 0)) for key in ("r", "g", "b", "w")}}
        self.saved_colors.append(saved)
        self._refresh_saved_colors()
        self._save_ui_preferences()

    def apply_saved_color(self, index):
        if 0 <= index < len(self.saved_colors):
            self._apply_rgbw_color(self.saved_colors[index]["rgbw"])

    def remove_saved_color(self, index):
        if not 0 <= index < len(self.saved_colors):
            return
        saved = self.saved_colors[index]
        if not messagebox.askyesno("Удалить цвет", f"Удалить «{saved['name']}» из палитры?", parent=self.root):
            return
        self.saved_colors.pop(index)
        self._refresh_saved_colors()
        self._save_ui_preferences()

    def _build_patch(self):
        self.patch_tab.grid_columnconfigure(0, weight=3)
        self.patch_tab.grid_columnconfigure(1, weight=2)
        self.patch_tab.grid_rowconfigure(0, weight=1)
        list_panel = self._panel(self.patch_tab, "СПИСОК ПАТЧА", "Одна вселенная · адреса приборов можно задавать вручную или автопатчем")
        list_panel.grid(row=0, column=0, sticky="nsew", padx=(0, 8), pady=4)
        self.patch_tree = ttk.Treeview(list_panel, columns=("name", "address", "group", "profile", "links"), show="headings", selectmode="browse")
        for key, title, width in [("name", "ПРИБОР", 140), ("address", "АДРЕС", 75), ("group", "ГРУППА", 105), ("profile", "ПРОФИЛЬ", 145), ("links", "СВЯЗЬ", 125)]:
            self.patch_tree.heading(key, text=title, command=lambda column=key: self._sort_from_patch_heading(column))
            self.patch_tree.column(key, width=width, anchor="w" if key in ("name", "group", "profile") else "center")
        self.patch_tree.pack(fill="both", expand=True, padx=10, pady=10)
        self.patch_tree.bind("<<TreeviewSelect>>", self._load_patch_form)
        self.patch_tree.bind("<Button-3>", self._fixture_context_menu)
        patch_buttons = tk.Frame(list_panel, bg=PANEL, padx=10, pady=8)
        patch_buttons.pack(fill="x")
        self._button(patch_buttons, "＋ Добавить PAR", self.add_fixture, small=True).pack(side="left")
        self._button(patch_buttons, "＋ Зеркальная группа", self.create_mirror_group, small=True).pack(side="left", padx=5)
        self._button(patch_buttons, "Удалить", self.remove_fixture, small=True).pack(side="left", padx=5)
        self._button(patch_buttons, "↑", lambda: self.move_fixture_order(-1), small=True).pack(side="right", padx=2)
        self._button(patch_buttons, "↓", lambda: self.move_fixture_order(1), small=True).pack(side="right", padx=2)
        step_row = tk.Frame(list_panel, bg=PANEL, padx=10)
        step_row.pack(fill="x", pady=(0, 10))
        tk.Label(step_row, text="ШАГ АВТОПАТЧА", fg=MUTED, bg=PANEL, font=("Segoe UI Semibold", 8)).pack(side="left", padx=(0, 8))
        self.patch_step_var = tk.StringVar(value="16 · Eurolite DMX 192")
        self.patch_step_combo = ttk.Combobox(step_row, textvariable=self.patch_step_var, state="readonly", width=27,
            values=("Ручной режим", "4 · RGBW", "5 · 5 каналов", "6 · 6 каналов", "8 · 8 каналов",
                    "10 · 10 каналов", "12 · 12 каналов", "16 · Eurolite DMX 192",
                    "24 · 24 канала", "32 · 32 канала", "Свой шаг…"))
        self.patch_step_combo.pack(side="left", padx=3)
        self.patch_step_entry_var = tk.StringVar(value="16")
        tk.Entry(step_row, textvariable=self.patch_step_entry_var, width=5, bg=PANEL_2, fg=TEXT,
                 insertbackground=TEXT, relief="flat", justify="center").pack(side="left", padx=5, ipady=5)
        self._button(step_row, "Применить автопатч", self.auto_patch, primary=True, small=True).pack(side="left", padx=4)

        edit = self._panel(self.patch_tab, "НАСТРОЙКА ПРИБОРА", "Начальный профиль RGBW можно уточнить, когда будет известен DMX-режим прожектора")
        edit.grid(row=0, column=1, sticky="nsew", padx=(8, 0), pady=4)
        form = tk.Frame(edit, bg=PANEL, padx=18, pady=8)
        form.pack(fill="both", expand=True)
        self.patch_vars = {key: tk.StringVar() for key in ("name", "address", "group", "r", "g", "b", "w")}
        for key, label in [("name", "ИМЯ ПРИБОРА"), ("address", "НАЧАЛЬНЫЙ DMX-АДРЕС"), ("group", "ГРУППА")]:
            tk.Label(form, text=label, fg=MUTED, bg=PANEL, font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(10, 4))
            if key == "group":
                widget = ttk.Combobox(form, textvariable=self.patch_vars[key], state="normal")
            else:
                widget = tk.Entry(form, textvariable=self.patch_vars[key], bg=PANEL_2, fg=TEXT,
                                  insertbackground=TEXT, relief="flat", font=("Segoe UI", 10))
            widget.pack(fill="x", ipady=7)
        tk.Label(form, text="КАНАЛЫ RGBW ВНУТРИ ПРОФИЛЯ", fg=MUTED, bg=PANEL,
                 font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(16, 5))
        tk.Label(form, text="Укажите номер канала от 1 до 16.", fg=MUTED, bg=PANEL,
                 font=("Segoe UI", 8)).pack(anchor="w", pady=(0, 6))
        offsetrow = tk.Frame(form, bg=PANEL)
        offsetrow.pack(fill="x")
        for key in ("r", "g", "b", "w"):
            part = tk.Frame(offsetrow, bg=PANEL)
            part.pack(side="left", expand=True, fill="x", padx=(0, 6))
            tk.Label(part, text=key.upper(), fg=TEXT, bg=PANEL, font=("Segoe UI Semibold", 8)).pack()
            tk.Entry(part, textvariable=self.patch_vars[key], bg=PANEL_2, fg=TEXT,
                     insertbackground=TEXT, relief="flat", justify="center", width=4).pack(fill="x", ipady=6)
        self._button(form, "Применить настройки прибора", self.apply_patch_form, primary=True).pack(fill="x", pady=(18, 8))
        tk.Label(form, text="По умолчанию: PAR RGBW · шаг 16 · адреса 1, 17, 33…\nШаг адресов можно изменить независимо от числа занятых каналов.",
                 fg=MUTED, bg=PANEL, font=("Segoe UI", 8), justify="left", wraplength=300).pack(anchor="w", pady=8)

    def _build_cues(self):
        self.cue_tab.grid_columnconfigure(0, weight=1)
        self.cue_tab.grid_rowconfigure(0, weight=1)
        panel = self._panel(self.cue_tab, "SNAPSHOTS", "Выберите snapshot, затем используйте FIRE, RECALL или UPDATE")
        panel.grid(row=0, column=0, sticky="nsew", pady=4)
        bar = tk.Frame(panel, bg=PANEL, padx=12, pady=8)
        bar.pack(fill="x")
        self._button(bar, "＋ Добавить выбранную сцену", self.add_cue, primary=True, small=True).pack(side="left")
        self._button(bar, "Изменить snapshot", self.edit_selected_cue, small=True).pack(side="left", padx=(5, 0))
        self._button(bar, "Удалить snapshot", self.remove_cue, small=True).pack(side="left", padx=5)
        self._button(bar, "↑", lambda: self.move_cue(-1), small=True).pack(side="left", padx=5)
        self._button(bar, "↓", lambda: self.move_cue(1), small=True).pack(side="left")
        self._button(bar, "FIRE", self.fire_selected_snapshot, primary=True, small=True).pack(side="left", padx=(18, 4))
        self._button(bar, "RECALL", self.recall_selected_snapshot, small=True).pack(side="left", padx=4)
        self._button(bar, "UPDATE ▾", self.open_snapshot_update_menu, small=True).pack(side="left", padx=4)
        tk.Checkbutton(bar, text="После FIRE выбрать следующий", variable=self.auto_preview_next_var,
                       bg=PANEL, fg=MUTED, selectcolor=PANEL_2, activebackground=PANEL,
                       activeforeground=TEXT, font=("Segoe UI", 8), command=self._save_ui_preferences).pack(side="left", padx=(10, 4))
        tk.Label(bar, text="ПЕРЕХОД (СЕК.)", fg=MUTED, bg=PANEL, font=("Segoe UI Semibold", 8)).pack(side="left", padx=(22, 6))
        tk.Entry(bar, textvariable=self.fade_var, width=6, bg=PANEL_2, fg=TEXT,
                 insertbackground=TEXT, relief="flat", justify="center").pack(side="left", ipady=6)
        tk.Label(bar, text="F2 · настройки snapshot", fg=MUTED, bg=PANEL,
                 font=("Segoe UI", 8)).pack(side="right", padx=(8, 0))
        body = tk.Frame(panel, bg=PANEL)
        body.pack(fill="both", expand=True, padx=12, pady=8)
        body.grid_columnconfigure(0, weight=3)
        body.grid_columnconfigure(1, weight=2)
        body.grid_rowconfigure(0, weight=1)
        self.cue_tree = ttk.Treeview(body, columns=("number", "name", "scene", "fade", "status"), show="headings", selectmode="extended")
        for key, title, width in [("number", "№", 55), ("name", "SNAPSHOT", 240), ("scene", "СЦЕНА", 240), ("fade", "ПЕРЕХОД", 100), ("status", "СОСТОЯНИЕ", 120)]:
            self.cue_tree.heading(key, text=title)
            self.cue_tree.column(key, width=width, anchor="center" if key != "scene" else "w")
        self.cue_tree.grid(row=0, column=0, sticky="nsew", padx=(0, 8))
        self.cue_tree.bind("<<TreeviewSelect>>", lambda _e: self._draw_next_cue_preview())
        self.cue_tree.bind("<Double-1>", lambda _e: self.edit_selected_cue())
        self.cue_tree.bind("<Button-3>", self._cue_context_menu)
        self.cue_tree.bind("<Motion>", self._on_cue_hover)
        self.cue_tree.bind("<Leave>", self._on_cue_leave)
        self.cue_tree.bind("<F2>", lambda _event: self.edit_selected_cue())
        self.root.bind_all("<KeyPress-space>", self._space_preview_press, add="+")
        self.root.bind_all("<KeyRelease-space>", self._space_preview_release, add="+")
        previews = tk.Frame(body, bg=PANEL)
        previews.grid(row=0, column=1, sticky="nsew")
        previews.grid_columnconfigure(0, weight=1)
        previews.grid_rowconfigure(0, weight=1)
        previews.grid_rowconfigure(1, weight=1)
        current_box = tk.Frame(previews, bg="#111820", highlightthickness=1, highlightbackground=LINE)
        current_box.grid(row=0, column=0, sticky="nsew", pady=(0, 5))
        self.current_scene_label = tk.Label(current_box, text="ТЕКУЩАЯ СЦЕНА · —", bg="#111820", fg=ACCENT,
                                            font=("Segoe UI Semibold", 9), anchor="w", padx=10, pady=7)
        self.current_scene_label.pack(fill="x")
        self.current_scene_canvas = tk.Canvas(current_box, bg="#111820", highlightthickness=0, height=175)
        self.current_scene_canvas.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self.current_scene_canvas.bind("<Configure>", lambda _event: self._draw_next_cue_preview())
        next_box = tk.Frame(previews, bg="#111820", highlightthickness=1, highlightbackground=LINE)
        next_box.grid(row=1, column=0, sticky="nsew", pady=(5, 0))
        self.next_scene_label = tk.Label(next_box, text="СЛЕДУЮЩАЯ СЦЕНА · —", bg="#111820", fg=TEXT,
                                         font=("Segoe UI Semibold", 9), anchor="w", padx=10, pady=7)
        self.next_scene_label.pack(fill="x")
        self.next_scene_canvas = tk.Canvas(next_box, bg="#111820", highlightthickness=0, height=175)
        self.next_scene_canvas.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self.next_scene_canvas.bind("<Configure>", lambda _event: self._draw_next_cue_preview())
        controls = tk.Frame(panel, bg=PANEL, padx=12, pady=12)
        controls.pack(fill="x")
        self.cue_status = tk.Label(controls, text="Snapshot не вызван", fg=MUTED, bg=PANEL,
                                   font=("Segoe UI", 9))
        self.cue_status.pack(side="left", padx=12)
        self._button(controls, "Сохранить состояние как сцену", self.store_scene, small=True).pack(side="right")

    def _build_stage_tab(self):
        panel = self._panel(self.stage_tab, "РЕДАКТОР СЦЕНЫ", "Раскладка общая для пульта и предпросмотра всех snapshots")
        panel.pack(fill="both", expand=True, pady=4)
        bar = tk.Frame(panel, bg=PANEL, padx=10, pady=8)
        bar.pack(fill="x")
        for label, kind in (("＋ Прожектор", "fixture"), ("＋ Музыкант", "musician"), ("＋ Метка", "label"),
                            ("＋ Прямоугольник", "rect"), ("＋ Круг", "circle")):
            button = self._button(bar, label, lambda k=kind: self._add_stage_object(k), small=True)
            button.pack(side="left", padx=2)
            button.bind("<ButtonPress-1>", lambda e, k=kind: self._stage_palette_drag_start(e, k), add="+")
            button.bind("<B1-Motion>", lambda e, k=kind: self._stage_palette_drag(e, k), add="+")
            button.bind("<ButtonRelease-1>", lambda e, k=kind: (self._stage_palette_drop(e, k), "break")[1])
        self._button(bar, "Размер сцены", self._edit_stage_dimensions, small=True).pack(side="left", padx=(8, 2))
        self._button(bar, "Изменить форму", self._edit_stage_object, small=True).pack(side="right", padx=2)
        self._button(bar, "Удалить", self._delete_stage_object, small=True).pack(side="right", padx=2)
        self.stage_canvas = tk.Canvas(panel, bg="#111820", highlightthickness=0)
        self.stage_canvas.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        self.stage_canvas.bind("<Configure>", lambda _e: self._draw_preview())
        self.stage_canvas.bind("<ButtonPress-1>", lambda e, c=self.stage_canvas: self._stage_press(e, c))
        self.stage_canvas.bind("<B1-Motion>", lambda e, c=self.stage_canvas: self._stage_motion(e, c))
        self.stage_canvas.bind("<ButtonRelease-1>", lambda e, c=self.stage_canvas: self._stage_release(e, c))
        self.stage_canvas.bind("<Double-1>", self._stage_double_click)
        self.stage_canvas.bind("<Button-3>", self._stage_context_menu)
        self.stage_canvases.append((self.stage_canvas, True))

    def _build_gangs(self):
        panel = self._panel(self.gang_panel, "GANGS · СВЯЗАННОЕ УПРАВЛЕНИЕ", "Управление выбранными приборами из консоли")
        panel.pack(fill="both", expand=True)
        bar = tk.Frame(panel, bg=PANEL, padx=12, pady=8)
        bar.pack(fill="x")
        self._button(bar, "＋ Создать из выбранных", self.create_gang, primary=True, small=True).pack(side="left")
        self._button(bar, "Включить выбранные", self.add_selected_to_gang, small=True).pack(side="left", padx=5)
        self._button(bar, "Исключить выбранные", self.remove_selected_from_gang, small=True).pack(side="left")
        self._button(bar, "Настроить каналы", self.edit_gang_scope, small=True).pack(side="left")
        self._button(bar, "Удалить gang", self.remove_gang, small=True).pack(side="left")
        self._button(bar, "Изолировать выбранные приборы", self.toggle_gang_isolation, small=True).pack(side="left", padx=5)
        self.gang_tree = ttk.Treeview(panel, columns=("name", "members", "scope"), show="headings", selectmode="browse")
        for key, title, width in [("name", "ИМЯ GANG", 220), ("members", "УЧАСТНИКИ", 360), ("scope", "СВЯЗАННЫЕ КАНАЛЫ", 300)]:
            self.gang_tree.heading(key, text=title)
            self.gang_tree.column(key, width=width, anchor="w")
        self.gang_tree.pack(fill="both", expand=True, padx=12, pady=8)
        note = "Выберите один прибор gang на вкладке «Пульт» и двигайте фейдер: остальные повторят шаг, сохраняя разницу значений. Состав группы и связанные каналы можно менять здесь. Изоляция временно отключает связь для выбранных приборов."
        tk.Label(panel, text=note, bg=PANEL, fg=MUTED, font=("Segoe UI", 9), wraplength=1000, justify="left").pack(anchor="w", padx=14, pady=(0, 12))

    def create_gang(self):
        members = self._selected_fixtures()
        if len(members) < 2:
            messagebox.showinfo("GANG", "Выберите на вкладке «Пульт» не менее двух приборов.")
            return
        occupied = {fixture_id for gang in self.show.get("gangs", []) for fixture_id in gang.get("members", [])}
        if any(fixture["id"] in occupied for fixture in members):
            messagebox.showerror("GANG", "Прибор может входить только в один gang. Удалите его из текущего gang перед созданием нового.")
            return
        name = simpledialog.askstring("Создать GANG", "Название группы:", initialvalue=f"GANG {len(self.show.get('gangs', [])) + 1}", parent=self.root)
        if not name or not name.strip():
            return
        self.show.setdefault("gangs", []).append({
            "id": uid(), "name": name.strip(), "members": [fixture["id"] for fixture in members],
            "scope": ["dimmer", "r", "g", "b", "w"],
        })
        self.gang_isolated_ids.difference_update(fixture["id"] for fixture in members)
        self.dirty = True
        self._refresh_gangs()

    def update_gang_members(self):
        selected = self.gang_tree.selection()
        members = self._selected_fixtures()
        if not selected:
            messagebox.showinfo("GANG", "Сначала выберите gang в этом списке.")
            return
        if len(members) < 2:
            messagebox.showinfo("GANG", "Выберите на вкладке «Пульт» не менее двух приборов для состава gang.")
            return
        gang = next((item for item in self.show.get("gangs", []) if item["id"] == selected[0]), None)
        if not gang:
            return
        selected_ids = {fixture["id"] for fixture in members}
        for other in self.show.get("gangs", []):
            if other["id"] != gang["id"] and selected_ids.intersection(other.get("members", [])):
                messagebox.showerror("GANG", "Выбранный прибор уже входит в другой gang.")
                return
        gang["members"] = [fixture["id"] for fixture in members]
        self.gang_isolated_ids.difference_update(selected_ids)
        self.dirty = True
        self._refresh_gangs()

    def add_selected_to_gang(self):
        selected = self.gang_tree.selection()
        fixtures = self._selected_fixtures()
        if not selected or not fixtures:
            messagebox.showinfo("GANG", "Выберите gang и приборы на вкладке «Пульт».")
            return
        gang = next((item for item in self.show.get("gangs", []) if item["id"] == selected[0]), None)
        if not gang:
            return
        other_members = {member for item in self.show.get("gangs", []) if item["id"] != gang["id"]
                         for member in item.get("members", [])}
        if any(fixture["id"] in other_members for fixture in fixtures):
            messagebox.showerror("GANG", "Часть выбранных приборов уже включена в другой gang.")
            return
        for fixture in fixtures:
            if fixture["id"] not in gang["members"]:
                gang["members"].append(fixture["id"])
            self.gang_isolated_ids.discard(fixture["id"])
        self.dirty = True
        self._refresh_gangs()

    def remove_selected_from_gang(self):
        selected = self.gang_tree.selection()
        fixtures = self._selected_fixtures()
        if not selected or not fixtures:
            messagebox.showinfo("GANG", "Выберите gang и приборы на вкладке «Пульт».")
            return
        gang = next((item for item in self.show.get("gangs", []) if item["id"] == selected[0]), None)
        if not gang:
            return
        remove_ids = {fixture["id"] for fixture in fixtures}
        before = len(gang["members"])
        gang["members"] = [member for member in gang["members"] if member not in remove_ids]
        self.gang_isolated_ids.difference_update(remove_ids)
        if len(gang["members"]) < 2:
            self.show["gangs"] = [item for item in self.show["gangs"] if item["id"] != gang["id"]]
        if len(gang.get("members", [])) != before:
            self.dirty = True
        self._refresh_gangs()

    def remove_gang(self):
        selected = self.gang_tree.selection()
        if not selected:
            return
        self.show["gangs"] = [gang for gang in self.show.get("gangs", []) if gang["id"] != selected[0]]
        self.dirty = True
        self._refresh_gangs()

    def edit_gang_scope(self):
        selected = self.gang_tree.selection()
        gang = next((item for item in self.show.get("gangs", []) if selected and item["id"] == selected[0]), None)
        if not gang:
            messagebox.showinfo("GANG", "Выберите gang в списке.")
            return
        dialog = tk.Toplevel(self.root)
        dialog.title(f"Каналы · {gang.get('name', 'GANG')}")
        dialog.configure(bg=PANEL)
        dialog.transient(self.root)
        dialog.grab_set()
        tk.Label(dialog, text="Какие каналы связывать при движении фейдера?", bg=PANEL, fg=TEXT,
                 font=("Segoe UI Semibold", 10)).pack(anchor="w", padx=16, pady=(14, 8))
        labels = [("dimmer", "Яркость"), ("r", "Красный"), ("g", "Зелёный"), ("b", "Синий"), ("w", "Белый")]
        variables = {}
        for key, label in labels:
            variable = tk.BooleanVar(value=key in gang.get("scope", []))
            variables[key] = variable
            tk.Checkbutton(dialog, text=label, variable=variable, bg=PANEL, fg=TEXT,
                           activebackground=PANEL, activeforeground=TEXT, selectcolor=PANEL_2).pack(anchor="w", padx=18)
        def save_scope():
            gang["scope"] = [key for key, _label in labels if variables[key].get()]
            self.dirty = True
            self._refresh_gangs()
            dialog.destroy()
        self._button(dialog, "Сохранить", save_scope, primary=True, small=True).pack(fill="x", padx=16, pady=14)

    def toggle_gang_isolation(self):
        members = self._selected_fixtures()
        if not members:
            messagebox.showinfo("GANG", "Выберите приборы на вкладке «Пульт».")
            return
        for fixture in members:
            fixture_id = fixture["id"]
            in_gang = any(fixture_id in gang.get("members", []) for gang in self.show.get("gangs", []))
            if not in_gang:
                messagebox.showinfo("GANG", f"{fixture['name']} не входит в gang.")
                continue
            if fixture_id in self.gang_isolated_ids:
                self.gang_isolated_ids.remove(fixture_id)
            else:
                self.gang_isolated_ids.add(fixture_id)
        self._refresh_gangs()

    def _refresh_gangs(self):
        if not getattr(self, "gang_tree", None):
            return
        for item in self.gang_tree.get_children():
            self.gang_tree.delete(item)
        fixtures = {fixture["id"]: fixture for fixture in self.show.get("fixtures", [])}
        labels = {"dimmer": "Яркость", "r": "Красный", "g": "Зелёный", "b": "Синий", "w": "Белый"}
        for gang in self.show.get("gangs", []):
            names = [fixtures[fid]["name"] + (" (ISO)" if fid in self.gang_isolated_ids else "")
                     for fid in gang.get("members", []) if fid in fixtures]
            scope = ", ".join(labels[key] for key in gang.get("scope", []) if key in labels)
            self.gang_tree.insert("", "end", iid=gang["id"], values=(gang.get("name", "GANG"), ", ".join(names), scope))
        if getattr(self, "fixture_list", None):
            self._refresh_fixture_list()
            self._refresh_patch_tree()

    def _refresh_ports(self):
        ports = self.output.available_ports()
        self.port_combo["values"] = ports
        if ports and not self.port_var.get():
            self.port_var.set(ports[0])
        if not ports and not self.output.connected:
            self.status_var.set("ОФЛАЙН-РЕЖИМ · COM-порт не найден · шоу сохраняется локально")

    def toggle_dmx(self):
        if self.output.connected:
            self.output.disconnect()
            self.connect_button.configure(text="Подключить DMX")
            self.status_dot.configure(fg=YELLOW)
            self.status_var.set("ОФЛАЙН-РЕЖИМ · DMX отключён · шоу сохраняется локально")
            return
        port = self.port_var.get().strip()
        if not port:
            self._refresh_ports()
            port = self.port_var.get().strip()
        if not port:
            messagebox.showinfo("Вывод DMX", "Выберите COM-порт интерфейса Eurolite. Офлайн-программирование доступно и без него.")
            return
        try:
            self.output.connect(port)
        except Exception as exc:
            messagebox.showerror("Подключение DMX", str(exc))
            return
        self.connect_button.configure(text="Отключить")
        self.status_dot.configure(fg=ACCENT)
        self.status_var.set(f"DMX ПОДКЛЮЧЁН · {port} · 512 каналов")
        self._make_dmx_frame()

    def _refresh_fixture_list(self):
        if not self.fixture_list:
            return
        self._selection_sync = True
        self.fixture_list.delete(0, "end")
        self._visible_fixtures = []
        filt = self.group_filter.get()
        for fixture in self._ordered_fixtures():
            if filt != "Все" and fixture["group"] != filt:
                continue
            self._visible_fixtures.append(fixture)
            active = "●" if fixture["id"] in self.selected_ids else "○"
            gang_name = self._gang_name_for_fixture(fixture["id"])
            badge = f"  ◆ {gang_name}" if gang_name else ""
            isolated = fixture["id"] in self.gang_isolated_ids
            if isolated:
                badge += " · ISO"
            self.fixture_list.insert("end", f"{active}  {fixture['name']}{badge}\n    Адр. {fixture['address']:03d}  ·  {fixture['group']}")
        for i, fixture in enumerate(self._visible_fixtures):
            if fixture["id"] in self.selected_ids:
                self.fixture_list.selection_set(i)
        self.root.after_idle(self._finish_fixture_selection_sync)
        self._sync_programmer()
        self._draw_preview()

    def _finish_fixture_selection_sync(self):
        self._selection_sync = False

    def _restore_fixture_selection(self, fixture_ids):
        self.selected_ids = set(fixture_ids)
        self._selection_sync = True
        self.fixture_list.selection_clear(0, "end")
        for index, fixture in enumerate(self._visible_fixtures):
            if fixture["id"] in self.selected_ids:
                self.fixture_list.selection_set(index)
        self._sync_programmer()
        self._draw_preview()
        self.root.after_idle(self._finish_fixture_selection_sync)

    def _gang_name_for_fixture(self, fixture_id):
        gang = next((item for item in self.show.get("gangs", []) if fixture_id in item.get("members", [])), None)
        return gang.get("name", "GANG") if gang else ""

    def _ordered_fixtures(self):
        fixtures = list(self.show["fixtures"])
        if self.fixture_sort_key == "name":
            fixtures.sort(key=lambda fixture: fixture.get("name", "").casefold(), reverse=self.fixture_sort_desc)
        elif self.fixture_sort_key == "address":
            fixtures.sort(key=lambda fixture: (fixture.get("address", 0), fixture.get("name", "").casefold()), reverse=self.fixture_sort_desc)
        elif self.fixture_sort_key == "group":
            fixtures.sort(key=lambda fixture: (fixture.get("group", "").casefold(), fixture.get("name", "").casefold()), reverse=self.fixture_sort_desc)
        return fixtures

    def _set_fixture_sort(self, label):
        self.fixture_sort_mode.set(label)
        self.fixture_sort_key = {"Порядок": "order", "Имя": "name", "Адрес": "address", "Группа": "group"}.get(label, "order")
        self.fixture_sort_desc = False
        self._refresh_fixture_list()
        self._refresh_patch_tree()

    def _sort_from_patch_heading(self, column):
        key = {"name": "name", "address": "address", "group": "group"}.get(column)
        if not key:
            key = "name"
        if self.fixture_sort_key == key:
            self.fixture_sort_desc = not self.fixture_sort_desc
        else:
            self.fixture_sort_key = key
            self.fixture_sort_desc = False
        self.fixture_sort_mode.set({"name": "Имя", "address": "Адрес", "group": "Группа"}[key])
        self._refresh_fixture_list()
        self._refresh_patch_tree()

    def move_fixture_order(self, direction):
        selected = self.patch_tree.selection()
        if not selected:
            return
        fixture_id = selected[0]
        fixtures = self._ordered_fixtures()
        index = next((i for i, fixture in enumerate(fixtures) if fixture["id"] == fixture_id), None)
        target = index + direction if index is not None else -1
        if index is None or not 0 <= target < len(fixtures):
            return
        fixtures[index], fixtures[target] = fixtures[target], fixtures[index]
        self.show["fixtures"] = fixtures
        self.fixture_sort_key = "order"
        self.fixture_sort_desc = False
        self.fixture_sort_mode.set("Порядок")
        self.dirty = True
        self._refresh_all()
        self.patch_tree.selection_set(fixture_id)
        self.patch_tree.see(fixture_id)

    def _refresh_all(self):
        self._ensure_stage_objects()
        groups = self.show.get("groups", ["Все"])
        groups[:] = ["Все" if group == "All" else group for group in groups]
        if "Все" not in groups:
            groups.insert(0, "Все")
        self.group_combo["values"] = groups
        self.assign_group["values"] = [g for g in groups if g != "Все"]
        self.patch_vars["group"].set(self.patch_vars["group"].get())
        self._refresh_fixture_list()
        self._refresh_patch_tree()
        self._refresh_scene_tree()
        self._refresh_cues()
        self._refresh_gangs()
        self.show_title.configure(text=self.show["name"])
        self._draw_preview()
        self._make_dmx_frame()

    def _on_fixture_select(self, _event=None):
        if self._selection_sync:
            return
        indexes = self.fixture_list.curselection()
        self.selected_ids = {self._visible_fixtures[i]["id"] for i in indexes if i < len(self._visible_fixtures)}
        self._sync_programmer()
        self._draw_preview()

    def _fixture_drag_start(self, event):
        if event.state & 0x0005:  # Shift or Ctrl selects several fixtures.
            self._fixture_drag_id = None
            return
        index = self.fixture_list.nearest(event.y)
        if 0 <= index < len(self._visible_fixtures):
            self._fixture_drag_id = self._visible_fixtures[index]["id"]
            selected = {fixture["id"] for index, fixture in enumerate(self._visible_fixtures)
                        if self.fixture_list.selection_includes(index)}
            self._fixture_drag_ids = selected if self._fixture_drag_id in selected else {self._fixture_drag_id}
            self._fixture_drag_start_y = event.y
            self._fixture_drag_start_x = event.x
            self._fixture_drag_active = False
            self._fixture_drop_index = None

    def _fixture_drop_slot(self, y):
        if not self._visible_fixtures:
            return 0
        y = max(0, min(y, max(0, self.fixture_list.winfo_height() - 1)))
        index = max(0, min(self.fixture_list.nearest(y), len(self._visible_fixtures) - 1))
        bounds = self.fixture_list.bbox(index)
        if not bounds:
            return index
        _x, row_y, _width, row_height = bounds
        return index if y < row_y + row_height / 2 else index + 1

    def _show_fixture_drop_indicator(self, slot):
        if not self.fixture_drop_indicator or not self._visible_fixtures:
            return
        slot = max(0, min(slot, len(self._visible_fixtures)))
        if slot == 0:
            bounds = self.fixture_list.bbox(0)
            line_y = bounds[1] if bounds else 0
        else:
            bounds = self.fixture_list.bbox(slot - 1)
            line_y = bounds[1] + bounds[3] if bounds else self.fixture_list.winfo_height() - 2
        self._fixture_drop_index = slot
        self.fixture_drop_indicator.place(x=0, y=max(0, line_y - 1), relwidth=1, height=3)
        self.fixture_drop_indicator.lift()

    def _hide_fixture_drop_indicator(self):
        if self.fixture_drop_indicator:
            self.fixture_drop_indicator.place_forget()

    def _fixture_drag_motion(self, event):
        if not self._fixture_drag_id:
            return
        if not self._fixture_drag_active:
            distance = max(abs(event.x - self._fixture_drag_start_x), abs(event.y - self._fixture_drag_start_y))
            if distance < 6:
                return
            self._fixture_drag_active = True
            self.fixture_list.configure(cursor="fleur")
        if event.y < 10:
            self.fixture_list.yview_scroll(-1, "units")
        elif event.y > self.fixture_list.winfo_height() - 10:
            self.fixture_list.yview_scroll(1, "units")
        self._show_fixture_drop_indicator(self._fixture_drop_slot(event.y))
        return "break"

    def _fixture_drag_release(self, event):
        fixture_id = self._fixture_drag_id
        drag_ids = set(self._fixture_drag_ids)
        active = self._fixture_drag_active
        self._fixture_drag_id = None
        self._fixture_drag_ids.clear()
        self._fixture_drag_active = False
        self.fixture_list.configure(cursor="")
        slot = self._fixture_drop_slot(event.y) if active else None
        self._hide_fixture_drop_indicator()
        self._fixture_drop_index = None
        if not fixture_id or not active or not self._visible_fixtures:
            return
        fixtures = self._ordered_fixtures()
        moving_ids = drag_ids.intersection(fixture["id"] for fixture in self._visible_fixtures)
        if not moving_ids:
            moving_ids = {fixture_id}
        moving = [fixture for fixture in fixtures if fixture["id"] in moving_ids]
        remaining = [fixture for fixture in fixtures if fixture["id"] not in moving_ids]
        visible_ids = [fixture["id"] for fixture in self._visible_fixtures]
        slot = max(0, min(slot if slot is not None else 0, len(visible_ids)))
        target_id = next((visible_ids[i] for i in range(slot, len(visible_ids)) if visible_ids[i] not in moving_ids), None)
        if target_id is not None:
            destination_index = next(i for i, fixture in enumerate(remaining) if fixture["id"] == target_id)
        else:
            last_visible_index = max((i for i, fixture in enumerate(remaining) if fixture["id"] in visible_ids), default=-1)
            destination_index = last_visible_index + 1 if slot >= len(visible_ids) else len(remaining)
        fixtures = remaining[:destination_index] + moving + remaining[destination_index:]
        if [fixture["id"] for fixture in fixtures] == [fixture["id"] for fixture in self.show["fixtures"]]:
            return "break"
        self.show["fixtures"] = fixtures
        self.fixture_sort_key = "order"
        self.fixture_sort_desc = False
        self.fixture_sort_mode.set("Порядок")
        self.selected_ids = moving_ids
        self.dirty = True
        self._refresh_all()
        self._restore_fixture_selection(moving_ids)
        first_visible_index = next((i for i, fixture in enumerate(self._visible_fixtures) if fixture["id"] in moving_ids), None)
        if first_visible_index is not None:
            self.fixture_list.see(first_visible_index)
        return "break"

    def _selected_fixtures(self):
        return [fixture for fixture in self.show["fixtures"] if fixture["id"] in self.selected_ids]

    def _sync_programmer(self):
        selected = self._selected_fixtures()
        if not selected:
            self.selection_label.configure(text="Прибор не выбран")
            self._mixed_fader_keys.clear()
            self._update_color_wheel_marker()
            return
        names = [x["name"] for x in selected]
        self.selection_label.configure(text=names[0] if len(names) == 1 else f"Выбрано приборов: {len(names)}")
        look = selected[0]["look"]
        self.slider_sync = True
        self._mixed_fader_keys.clear()
        for key, scale in self.faders.items():
            mixed = any(x["look"].get(key, 0) != look.get(key, 0) for x in selected)
            value = look.get(key, 0)
            if mixed:
                self._mixed_fader_keys.add(key)
            scale.set(value)
            self.fader_labels[key].configure(text="РАЗНЫЕ" if mixed else str(round(value)))
            self._gang_fader_previous[key] = value
        self.slider_sync = False
        self._update_color_wheel_marker()

    def _on_fader(self, key, value):
        self.fader_labels[key].configure(text=str(value))
        if self.slider_sync:
            return
        selected = self._selected_fixtures()
        previous = self._gang_fader_previous.get(key, value)
        delta = value - previous
        selected_ids = {fixture["id"] for fixture in selected}
        linked_gang = next((gang for gang in self.show.get("gangs", [])
                            if key in gang.get("scope", []) and selected_ids
                            and selected_ids.issubset(set(gang.get("members", [])))), None)
        targets = selected
        if linked_gang and not selected_ids.intersection(self.gang_isolated_ids):
            targets = [fixture for fixture in self.show["fixtures"]
                       if fixture["id"] in linked_gang.get("members", [])
                       and fixture["id"] not in self.gang_isolated_ids]
        elif len(selected) == 1 and selected[0]["id"] not in self.gang_isolated_ids:
            gang = next((item for item in self.show.get("gangs", [])
                         if selected[0]["id"] in item.get("members", []) and key in item.get("scope", [])), None)
            if gang:
                targets = [fixture for fixture in self.show["fixtures"]
                           if fixture["id"] in gang.get("members", [])
                           and fixture["id"] not in self.gang_isolated_ids]
        self._apply_fader_delta(targets, key, delta)
        self._gang_fader_previous[key] = value
        self._mixed_fader_keys.discard(key)
        self.fader_labels[key].configure(text=str(value))
        self.dirty = True
        self._draw_preview()
        self._draw_next_cue_preview()
        self._make_dmx_frame()
        self._auto_update_snapshots((key,))

    def _apply_fader_delta(self, fixtures, key, delta):
        processed = set()
        for fixture in fixtures:
            mirror_id = fixture.get("mirror_group_id")
            token = mirror_id or fixture["id"]
            if token in processed:
                continue
            processed.add(token)
            new_value = max(0, min(255, fixture["look"].get(key, 0) + delta))
            fixture["look"][key] = new_value
            if mirror_id:
                for mirror in self.show["fixtures"]:
                    if mirror.get("mirror_group_id") == mirror_id:
                        mirror["look"][key] = new_value

    def _color_targets(self, selected, key):
        selected_ids = {fixture["id"] for fixture in selected}
        gang = next((item for item in self.show.get("gangs", [])
                     if key in item.get("scope", []) and selected_ids
                     and selected_ids.issubset(set(item.get("members", [])))), None)
        if gang and not selected_ids.intersection(self.gang_isolated_ids):
            return [fixture for fixture in self.show["fixtures"]
                    if fixture["id"] in gang.get("members", [])
                    and fixture["id"] not in self.gang_isolated_ids]
        if len(selected) == 1 and selected[0]["id"] not in self.gang_isolated_ids:
            gang = next((item for item in self.show.get("gangs", [])
                         if selected[0]["id"] in item.get("members", []) and key in item.get("scope", [])), None)
            if gang:
                return [fixture for fixture in self.show["fixtures"]
                        if fixture["id"] in gang.get("members", [])
                        and fixture["id"] not in self.gang_isolated_ids]
        return selected

    def _apply_rgbw_color(self, values):
        selected = self._selected_fixtures()
        if not selected:
            return
        reference = selected[0]["look"]
        for key in ("r", "g", "b", "w"):
            delta = round(values[key]) - reference.get(key, 0)
            self._apply_fader_delta(self._color_targets(selected, key), key, delta)
        if reference.get("dimmer", 0) == 0:
            self._apply_fader_delta(self._color_targets(selected, "dimmer"), "dimmer", 255)
        self.dirty = True
        self._sync_programmer()
        self._draw_preview()
        self._draw_next_cue_preview()
        self._make_dmx_frame()
        self._auto_update_snapshots(("r", "g", "b", "w", "dimmer"))

    def _auto_update_snapshots(self, changed_channels):
        selected = set(self.cue_tree.selection()) if getattr(self, "cue_tree", None) else set()
        if not selected:
            return
        live = {fixture["id"]: fixture["look"] for fixture in self.show.get("fixtures", [])}
        changed = False
        for cue in self.show.get("cues", []):
            if cue.get("id") not in selected or cue.get("update_method") != "auto":
                continue
            scope = set(cue.get("update_fixtures", [])) or set(live)
            channels = set(cue.get("update_channels", changed_channels)).intersection(changed_channels)
            look = cue.setdefault("look", {})
            for fixture_id in scope.intersection(live):
                target = look.setdefault(fixture_id, blank_look())
                for channel in channels:
                    target[channel] = live[fixture_id].get(channel, 0)
                    changed = True
        if changed:
            self.dirty = True
            self._draw_next_cue_preview()

    def set_hex_color(self, hex_color):
        rgb = tuple(int(hex_color[i:i + 2], 16) for i in (1, 3, 5))
        white = min(rgb)
        self._apply_rgbw_color({"r": rgb[0] - white, "g": rgb[1] - white,
                                "b": rgb[2] - white, "w": white})

    def assign_selected_group(self):
        group = self.assign_group.get().strip()
        if not group:
            messagebox.showinfo("Группа", "Введите или выберите название группы.")
            return
        if group not in self.show["groups"]:
            self.show["groups"].append(group)
        selected_ids = set(self.selected_ids)
        self.group_filter.set("Все")
        for fixture in self._selected_fixtures():
            fixture["group"] = group
        self.selected_ids = selected_ids
        self.dirty = True
        self._refresh_all()
        self.root.after_idle(lambda ids=selected_ids: self._restore_fixture_selection(ids))

    def open_selected_patch_editor(self):
        selected = self._selected_fixtures()
        if not selected:
            messagebox.showinfo("Патч", "Выберите прибор в списке консоли.")
            return
        fixture_id = selected[0]["id"]
        self.tabs.select(self.patch_tab)
        self.patch_tree.selection_set(fixture_id)
        self.patch_tree.focus(fixture_id)
        self.patch_tree.see(fixture_id)
        self._load_patch_form()

    def _draw_preview(self):
        if not self.preview_canvas:
            return
        self._update_live_snapshot_label()
        for canvas, editable in list(self.stage_canvases):
            try:
                self._render_stage(canvas, editable)
            except tk.TclError:
                self.stage_canvases = [(item, mode) for item, mode in self.stage_canvases if item != canvas]
        if self._fade:
            canvas = self.preview_canvas
            width = max(canvas.winfo_width(), 400)
            progress = min(1, max(0, (time.monotonic() - self._fade["started"]) / self._fade["duration"]))
            canvas.create_rectangle(18, 8, width - 18, 13, fill=PANEL_2, outline="")
            canvas.create_rectangle(18, 8, 18 + (width - 36) * progress, 13, fill=ACCENT, outline="")
            canvas.create_text(18, 19, text=self._fade.get("label", "ПЕРЕХОД СЦЕНЫ"), anchor="nw",
                               fill=ACCENT, font=("Segoe UI Semibold", 8))

    def _update_live_snapshot_label(self):
        if not getattr(self, "live_snapshot_label", None):
            return
        index = getattr(self, "current_cue", -1)
        cues = self.show.get("cues", [])
        if 0 <= index < len(cues):
            cue = cues[index]
            scene = next((item for item in self.show.get("scenes", []) if item["id"] == cue.get("scene_id")), None)
            name = cue.get("label", scene.get("name", "" ) if scene else "Snapshot")
            self.live_snapshot_label.configure(text=f"LIVE · SNAPSHOT {index + 1:02d} · {name}")
        else:
            self.live_snapshot_label.configure(text="LIVE · РУЧНОЕ СОСТОЯНИЕ · SNAPSHOT НЕ ВЫЗВАН")

    def _ensure_stage_objects(self):
        stage = self.show.setdefault("stage", {"objects": []})
        if not isinstance(stage, dict):
            stage = self.show["stage"] = {"objects": []}
        stage.setdefault("width_m", 8); stage.setdefault("depth_m", 6)
        objects = stage.setdefault("objects", [])
        existing = {item.get("fixture_id") for item in objects if isinstance(item, dict) and item.get("kind") == "fixture"}
        fixtures = self.show.get("fixtures", [])
        for index, fixture in enumerate(fixtures):
            if fixture["id"] in existing:
                continue
            col = index % 6
            row = index // 6
            objects.append({"id": f"stage-{fixture['id']}", "kind": "fixture", "fixture_id": fixture["id"],
                            "x": 0.14 + col * 0.145, "y": 0.25 + row * 0.26, "w": 0.10, "h": 0.13})
        for item in objects:
            if isinstance(item, dict):
                item.setdefault("x", 0.5); item.setdefault("y", 0.5)
                item.setdefault("w", 0.14); item.setdefault("h", 0.14)
                item.setdefault("label", "Объект"); item.setdefault("color", "#61d9c3")
        return objects

    def _render_stage(self, canvas, editable=False, look_override=None, actual=False):
        canvas.delete("all")
        width, height = max(canvas.winfo_width(), 280), max(canvas.winfo_height(), 120)
        canvas.create_rectangle(0, 0, width, height, fill="#111820", outline="")
        left, top, right, bottom = width * .06, height * .08, width * .94, height * .92
        canvas.create_rectangle(left, top, right, bottom, fill="#202a35", outline="#536273", width=2)
        canvas.create_rectangle(left + 8, top + 8, right - 8, top + 8 + max(22, height * .11), fill="#293746", outline="")
        canvas.create_text((left + right) / 2, top + 18, text="ЗАДНИК СЦЕНЫ", fill="#b8c5d3", font=("Segoe UI Semibold", 8))
        stage_data = self.show.get("stage", {})
        canvas.create_text((left + right) / 2, bottom - 10, text=f"РАЗМЕР СЦЕНЫ  ·  {stage_data.get('width_m', 8)} × {stage_data.get('depth_m', 6)} м",
                           fill="#78899a", font=("Segoe UI", 8))
        fixture_by_id = {item["id"]: item for item in self.show.get("fixtures", [])}
        fixture_bounds = {}
        for obj in self._ensure_stage_objects():
            x, y = obj["x"] * width, obj["y"] * height
            w, h = max(14, obj["w"] * width), max(14, obj["h"] * height)
            kind = obj.get("kind")
            if kind == "fixture":
                fixture = fixture_by_id.get(obj.get("fixture_id"))
                if not fixture:
                    continue
                fixture_bounds[fixture["id"]] = (x - w / 2, y - h / 2, x + w / 2, y + h / 2)
                look = (look_override or {}).get(fixture["id"], fixture.get("look", blank_look()))
                intensity = 0 if actual and self.blackout_active else max(0, min(1, look.get("dimmer", 0) / 255))
                channels = [min(255, round(look.get(c, 0) * intensity + look.get("w", 0) * intensity * .72)) for c in ("r", "g", "b")]
                color = "#%02x%02x%02x" % tuple(channels)
                radius = max(6, min(w, h) * .28)
                canvas.create_oval(x - radius, y - radius, x + radius, y + radius, fill=color, outline=ACCENT if fixture["id"] in self.selected_ids else "#8393a3", width=2)
                canvas.create_text(x, y + radius + 10, text=fixture["name"], fill=TEXT, font=("Segoe UI Semibold", max(7, min(10, int(width / 100)))))
                canvas.create_text(x, y - radius - 6, text=f"{fixture['address']:03d}", fill=MUTED, font=("Consolas", 7))
            else:
                fill = obj.get("color", "#61d9c3")
                outline = ACCENT if editable and obj.get("id") == self.stage_selected_id else fill
                if kind == "musician":
                    canvas.create_oval(x - w / 2, y - h / 2, x + w / 2, y + h / 2, fill=fill, outline=outline, width=2)
                elif kind == "circle":
                    canvas.create_oval(x - w / 2, y - h / 2, x + w / 2, y + h / 2, fill=fill, outline=outline, width=2)
                else:
                    canvas.create_rectangle(x - w / 2, y - h / 2, x + w / 2, y + h / 2, fill=fill, outline=outline, width=2)
                canvas.create_text(x, y, text=obj.get("label", "Объект"), fill="#101319" if fill.lower() != "#101319" else TEXT,
                                   font=("Segoe UI Semibold", 9), width=max(25, w - 8))
                if editable and obj.get("id") == self.stage_selected_id:
                    canvas.create_rectangle(x + w/2 - 5, y + h/2 - 5, x + w/2 + 5, y + h/2 + 5, fill=ACCENT, outline="", tags=("resize",))
        if canvas == self.preview_canvas:
            self.preview_bounds = fixture_bounds

    def open_stage_editor(self):
        self.tabs.select(self.stage_tab)
        self._draw_preview()

    def _stage_palette_drag_start(self, event, kind):
        self.stage_drag = {"palette": kind, "start_x": event.x_root, "start_y": event.y_root, "moved": False}

    def _stage_palette_drag(self, event, kind):
        if self.stage_drag and self.stage_drag.get("palette") == kind:
            if abs(event.x_root-self.stage_drag["start_x"]) + abs(event.y_root-self.stage_drag["start_y"]) > 5:
                self.stage_drag["moved"] = True

    def _stage_palette_drop(self, event, kind):
        drag, self.stage_drag = self.stage_drag, None
        if not drag:
            return
        if not drag.get("moved"):
            self._add_stage_object(kind)
            return
        canvas = self.stage_canvas
        x = event.x_root - canvas.winfo_rootx()
        y = event.y_root - canvas.winfo_rooty()
        if 0 <= x <= canvas.winfo_width() and 0 <= y <= canvas.winfo_height():
            self._add_stage_object(kind, x / max(1, canvas.winfo_width()), y / max(1, canvas.winfo_height()))

    def _stage_context_menu(self, event):
        canvas = event.widget
        canvas.focus_set()
        obj = self._stage_hit(canvas, event.x, event.y)
        menu = tk.Menu(self.root, tearoff=0, bg=PANEL, fg=TEXT, activebackground=ACCENT, activeforeground="#10151b")
        if obj:
            self.stage_selected_id = obj["id"]
            self._draw_preview()
            if obj.get("kind") == "fixture":
                self.selected_ids = {obj.get("fixture_id")}
                self._context_kind = "fixture"
                self._add_context_commands(menu, "fixture")
                menu.add_separator()
                menu.add_command(label="Показать настройки прибора", command=lambda: self._open_fixture_patch(obj.get("fixture_id")))
            else:
                self._context_kind = "stage"
                self._add_context_commands(menu, "stage")
        else:
            self.stage_selected_id = None
            self._context_kind = "stage"
            menu.add_command(label="Вставить", command=lambda: self._paste_context("stage"),
                             state="normal" if self._app_clipboard and self._app_clipboard.get("kind") == "stage" else "disabled")
            menu.add_separator()
            x = max(.06, min(.94, event.x / max(1, canvas.winfo_width())))
            y = max(.08, min(.92, event.y / max(1, canvas.winfo_height())))
            for title, kind in (("Музыкант", "musician"), ("Метка", "label"), ("Прямоугольник", "rect"), ("Круг", "circle")):
                menu.add_command(label=f"Добавить: {title}", command=lambda k=kind, px=x, py=y: self._add_stage_object(k, px, py))
        self._popup_context_menu(menu, event)

    def _stage_double_click(self, event):
        obj = self._stage_hit(event.widget, event.x, event.y)
        if obj and obj.get("kind") != "fixture":
            self.stage_selected_id = obj["id"]
            self._edit_stage_object()

    def _open_fixture_patch(self, fixture_id):
        self.selected_ids = {fixture_id}
        self.tabs.select(self.patch_tab)
        self.patch_tree.selection_set(fixture_id)
        self.patch_tree.focus(fixture_id)
        self.patch_tree.see(fixture_id)
        self._load_patch_form()

    def _fixture_context_menu(self, event):
        event.widget.focus_set()
        if event.widget is self.patch_tree:
            row = self.patch_tree.identify_row(event.y)
            fixture = next((item for item in self.show["fixtures"] if row and item.get("id") == row), None)
        else:
            index = self.fixture_list.nearest(event.y)
            fixture = self._visible_fixtures[index] if 0 <= index < len(getattr(self, "_visible_fixtures", [])) else None
        if fixture:
            self.selected_ids = {fixture["id"]}
            if event.widget is self.patch_tree:
                self.patch_tree.selection_set(fixture["id"])
                self.patch_tree.focus(fixture["id"])
            else:
                self._refresh_fixture_list()
        else:
            return
        self._context_kind = "fixture"
        menu = tk.Menu(self.root, tearoff=0, bg=PANEL, fg=TEXT, activebackground=ACCENT, activeforeground="#10151b")
        self._add_context_commands(menu, "fixture")
        menu.add_separator()
        menu.add_command(label="Показать на сцене", command=lambda: self.tabs.select(self.stage_tab))
        self._popup_context_menu(menu, event)

    def _scene_context_menu(self, event):
        self.scene_tree.focus_set()
        row = self.scene_tree.identify_row(event.y)
        if not row:
            return
        self.scene_tree.selection_set(row)
        self._context_kind = "scene"
        menu = tk.Menu(self.root, tearoff=0, bg=PANEL, fg=TEXT, activebackground=ACCENT, activeforeground="#10151b")
        self._add_context_commands(menu, "scene")
        menu.add_separator()
        menu.add_command(label="Вызвать сцену", command=self.recall_selected_scene)
        menu.add_command(label="Добавить в snapshots", command=self.add_selected_scene_to_cue)
        self._popup_context_menu(menu, event)

    def _cue_context_menu(self, event):
        self.cue_tree.focus_set()
        row = self.cue_tree.identify_row(event.y)
        if not row:
            return
        self.cue_tree.selection_set(row)
        self.cue_tree.focus(row)
        self._context_kind = "cue"
        menu = tk.Menu(self.root, tearoff=0, bg=PANEL, fg=TEXT, activebackground=ACCENT, activeforeground="#10151b")
        self._add_context_commands(menu, "cue")
        menu.add_separator()
        menu.add_command(label="FIRE", command=self.fire_selected_snapshot)
        menu.add_command(label="RECALL", command=self.recall_selected_snapshot)
        self._popup_context_menu(menu, event)

    def _popup_context_menu(self, menu, event):
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                menu.grab_release()
            except tk.TclError:
                pass

    def _edit_stage_dimensions(self):
        stage = self.show.setdefault("stage", {"objects": []})
        width = simpledialog.askinteger("Размер сцены", "Ширина сцены, м:", initialvalue=stage.get("width_m", 8), minvalue=1, maxvalue=100, parent=self.root)
        if width is None:return
        depth = simpledialog.askinteger("Размер сцены", "Глубина сцены, м:", initialvalue=stage.get("depth_m", 6), minvalue=1, maxvalue=100, parent=self.root)
        if depth is None:return
        stage.update(width_m=width,depth_m=depth);self.dirty=True;self._draw_preview()

    def _add_stage_object(self, kind, x=.5, y=.5):
        objects = self._ensure_stage_objects()
        if kind == "fixture":
            used = {item.get("fixture_id") for item in objects if item.get("kind") == "fixture"}
            fixture = next((item for item in self.show["fixtures"] if item["id"] not in used), None)
            if not fixture:
                messagebox.showinfo("Сцена", "Все приборы уже размещены на сцене."); return
            item = {"id": f"stage-{fixture['id']}", "kind": kind, "fixture_id": fixture["id"], "x": x, "y": y, "w": .1, "h": .13}
        else:
            labels = {"musician": "Музыкант", "label": "Метка", "rect": "Объект", "circle": "Объект"}
            item = {"id": uid(), "kind": kind, "label": labels.get(kind, "Объект"), "color": "#61d9c3", "x": x, "y": y, "w": .14, "h": .12}
            objects.append(item)
        self.stage_selected_id = item["id"]; self.dirty = True; self._draw_preview()
        if kind != "fixture": self._edit_stage_object()

    def _stage_hit(self, canvas, x, y):
        width, height = max(1, canvas.winfo_width()), max(1, canvas.winfo_height())
        for obj in reversed(self._ensure_stage_objects()):
            if obj.get("kind") == "fixture":
                continue
            cx, cy = obj["x"]*width, obj["y"]*height
            if abs(x-cx) <= obj["w"]*width/2 and abs(y-cy) <= obj["h"]*height/2:
                return obj
        for obj in reversed(self._ensure_stage_objects()):
            if obj.get("kind") != "fixture":
                continue
            cx, cy = obj["x"] * width, obj["y"] * height
            if abs(x-cx) <= obj["w"]*width/2 and abs(y-cy) <= obj["h"]*height/2:
                return obj
        return None

    def _stage_press(self, event, canvas):
        canvas.focus_set()
        self._context_kind = "stage"
        obj = self._stage_hit(canvas,event.x,event.y)
        if not obj: self.stage_selected_id=None; self.stage_drag=None; self._draw_preview(); return
        self.stage_selected_id=obj["id"]
        self.stage_drag={"id":obj["id"],"x":event.x,"y":event.y,"resize":event.x>obj["x"]*canvas.winfo_width()+obj["w"]*canvas.winfo_width()/2-12 and event.y>obj["y"]*canvas.winfo_height()+obj["h"]*canvas.winfo_height()/2-12}
        if obj.get("kind")=="fixture":
            self.selected_ids={obj["fixture_id"]}; self._refresh_fixture_list()
        self._draw_preview()

    def _stage_motion(self,event,canvas):
        if not self.stage_drag or "id" not in self.stage_drag:return
        obj=next((item for item in self._ensure_stage_objects() if item["id"]==self.stage_drag["id"]),None)
        if not obj:return
        dx,dy=event.x-self.stage_drag["x"],event.y-self.stage_drag["y"]
        if self.stage_drag.get("resize"):
            obj["w"]=max(.035,min(.6,obj["w"]+dx/max(1,canvas.winfo_width())))
            obj["h"]=max(.04,min(.6,obj["h"]+dy/max(1,canvas.winfo_height())))
        else:
            obj["x"]=max(.06,min(.94,obj["x"]+dx/max(1,canvas.winfo_width())))
            obj["y"]=max(.08,min(.92,obj["y"]+dy/max(1,canvas.winfo_height())))
        self.stage_drag["x"],self.stage_drag["y"]=event.x,event.y
        self.dirty=True;self._draw_preview()

    def _stage_release(self,event,canvas):self.stage_drag=None

    def _edit_stage_object(self):
        obj=next((item for item in self._ensure_stage_objects() if item["id"]==self.stage_selected_id),None)
        if not obj or obj.get("kind")=="fixture":return
        if self.stage_edit_overlay:
            self.stage_edit_overlay.destroy()
        overlay = tk.Frame(self.stage_tab, bg=PANEL, highlightthickness=1, highlightbackground=LINE,
                           padx=18, pady=16, width=470, height=520)
        original = copy.deepcopy(obj)
        self.stage_edit_overlay = overlay
        overlay.pack_propagate(False)
        overlay.place(relx=.5, rely=.5, anchor="center", width=470, height=520)
        overlay.lift()
        title = tk.Label(overlay, text="НАСТРОЙКА ОБЪЕКТА СЦЕНЫ  ·  ПЕРЕТАЩИТЕ, ЧТОБЫ ПЕРЕМЕСТИТЬ",
                         bg=PANEL, fg=ACCENT, cursor="fleur", font=("Segoe UI Semibold", 10))
        title.pack(anchor="w", pady=(0, 12))
        self._bind_floating_panel(overlay, title)
        form = tk.Frame(overlay, bg=PANEL); form.pack(fill="both", expand=True)
        label_var = tk.StringVar(value=obj.get("label", "Объект"))
        kind_names = {"label": "Метка", "musician": "Музыкант", "rect": "Прямоугольник", "circle": "Круг"}
        name_kinds = {value: key for key, value in kind_names.items()}
        kind_var = tk.StringVar(value=kind_names.get(obj.get("kind", "label"), "Метка"))
        source_color = obj.get("color", "#61d9c3")
        if len(source_color) == 4:
            source_color = "#" + "".join(char * 2 for char in source_color[1:])
        try:
            initial_rgb = tuple(int(source_color[index:index + 2], 16) for index in (1, 3, 5))
        except (ValueError, TypeError):
            initial_rgb = (97, 217, 195)
        rgb_vars = {channel: tk.IntVar(value=value) for channel, value in zip(("R", "G", "B"), initial_rgb)}
        initial_hex = "#%02X%02X%02X" % initial_rgb
        width_var = tk.DoubleVar(value=round(obj.get("w", .14) * 100))
        height_var = tk.DoubleVar(value=round(obj.get("h", .12) * 100))
        x_var = tk.DoubleVar(value=round(obj.get("x", .5) * 100))
        y_var = tk.DoubleVar(value=round(obj.get("y", .5) * 100))
        rows = [("НАЗВАНИЕ", tk.Entry(form, textvariable=label_var, bg=PANEL_2, fg=TEXT, insertbackground=TEXT, relief="flat")),
                ("ФОРМА", ttk.Combobox(form, textvariable=kind_var, values=tuple(kind_names.values()), state="readonly"))]
        for row, (title, widget) in enumerate(rows):
            tk.Label(form, text=title, bg=PANEL, fg=MUTED, font=("Segoe UI Semibold", 8)).grid(row=row, column=0, sticky="w", padx=(0, 12), pady=6)
            widget.grid(row=row, column=1, sticky="ew", pady=6, ipady=4)
        form.grid_columnconfigure(1, weight=1)
        color_row = tk.Frame(form, bg=PANEL); color_row.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(6, 2))
        color_row.grid_columnconfigure(1, weight=1)
        tk.Label(color_row, text="ЦВЕТ", bg=PANEL, fg=MUTED, font=("Segoe UI Semibold", 8)).grid(row=0, column=0, sticky="w", padx=(0, 12))
        initial_text_color = "#101319" if sum(initial_rgb) / 3 > 145 else "#ffffff"
        color_swatch = tk.Label(color_row, text=initial_hex, bg=initial_hex, fg=initial_text_color, width=10, padx=8, pady=3,
                                font=("Consolas", 8, "bold"))
        color_swatch.grid(row=0, column=1, sticky="e")
        def current_hex():
            return "#%02X%02X%02X" % tuple(rgb_vars[channel].get() for channel in ("R", "G", "B"))
        def preview_form():
            obj["color"] = current_hex()
            rgb = tuple(rgb_vars[channel].get() for channel in ("R", "G", "B"))
            color_swatch.configure(text=obj["color"], bg=obj["color"], fg="#101319" if sum(rgb) / 3 > 145 else "#ffffff")
            self._stage_form_preview(obj, width_var, height_var, x_var, y_var)
        for row, (channel, channel_color) in enumerate((("R", "#ff687a"), ("G", "#53d69a"), ("B", "#6494ff")), start=3):
            tk.Label(form, text=channel, bg=PANEL, fg=channel_color, font=("Segoe UI Semibold", 8)).grid(row=row, column=0, sticky="w", padx=(0, 12))
            color_scale = tk.Scale(form, from_=0, to=255, orient="horizontal", variable=rgb_vars[channel],
                                   bg=PANEL, fg=TEXT, activebackground=channel_color, highlightthickness=0,
                                   troughcolor=channel_color, length=260, command=lambda _value: preview_form())
            color_scale.bind("<ButtonPress-1>", self._history_interaction_start, add="+")
            color_scale.grid(row=row, column=1, sticky="ew")
        for row, (title_text, variable, end) in enumerate((("ШИРИНА %", width_var, 60), ("ВЫСОТА %", height_var, 60),
                                                            ("ПОЗИЦИЯ X %", x_var, 94), ("ПОЗИЦИЯ Y %", y_var, 92)), start=6):
            tk.Label(form, text=title_text, bg=PANEL, fg=MUTED, font=("Segoe UI Semibold", 8)).grid(row=row, column=0, sticky="w", padx=(0, 12))
            form_scale = tk.Scale(form, from_=4 if row < 5 else 6, to=end, orient="horizontal", variable=variable,
                                  bg=PANEL, fg=TEXT, highlightthickness=0, troughcolor=PANEL_2, length=260,
                                  command=lambda _value: self._stage_form_preview(obj, width_var, height_var, x_var, y_var))
            form_scale.bind("<ButtonPress-1>", self._history_interaction_start, add="+")
            form_scale.grid(row=row, column=1, sticky="ew")
        buttons = tk.Frame(overlay, bg=PANEL); buttons.pack(fill="x", pady=(12, 0))
        def close(restore=False):
            if restore:
                obj.clear(); obj.update(original)
            if overlay.winfo_exists(): overlay.destroy()
            if self.stage_edit_overlay == overlay: self.stage_edit_overlay = None
            if restore: self._draw_preview()
        def save():
            color = current_hex()
            obj.update(label=label_var.get().strip() or "Объект", kind=name_kinds.get(kind_var.get(), "label"), color=color,
                       w=width_var.get()/100, h=height_var.get()/100, x=x_var.get()/100, y=y_var.get()/100)
            self.dirty = True; close(); self._draw_preview()
        self._button(buttons, "Отмена", lambda: close(restore=True), small=True).pack(side="right", padx=3)
        self._button(buttons, "Сохранить", save, primary=True, small=True).pack(side="right", padx=3)

    def _stage_form_preview(self, obj, width_var, height_var, x_var, y_var):
        obj.update(w=width_var.get()/100, h=height_var.get()/100, x=x_var.get()/100, y=y_var.get()/100)
        self._draw_preview()

    def _bind_floating_panel(self, panel, handle):
        handle.bind("<ButtonPress-1>", lambda event, target=panel: self._floating_panel_start(event, target))
        handle.bind("<B1-Motion>", lambda event, target=panel: self._floating_panel_move(event, target))

    def _floating_panel_start(self, event, panel):
        panel._floating_offset_x = event.x_root - panel.winfo_rootx()
        panel._floating_offset_y = event.y_root - panel.winfo_rooty()

    def _floating_panel_move(self, event, panel):
        parent = panel.master
        x = event.x_root - parent.winfo_rootx() - panel._floating_offset_x
        y = event.y_root - parent.winfo_rooty() - panel._floating_offset_y
        x = max(0, min(x, max(0, parent.winfo_width() - panel.winfo_width())))
        y = max(0, min(y, max(0, parent.winfo_height() - panel.winfo_height())))
        panel.place_configure(relx=0, rely=0, anchor="nw", x=x, y=y)

    def _delete_stage_object(self):
        if not self.stage_selected_id:return
        self._checkpoint_undo()
        if self.stage_edit_overlay and self.stage_edit_overlay.winfo_exists():
            self.stage_edit_overlay.destroy(); self.stage_edit_overlay = None
        self.show["stage"]["objects"]=[item for item in self._ensure_stage_objects() if item.get("id")!=self.stage_selected_id]
        self.stage_selected_id=None;self.dirty=True;self._draw_preview()

    def _on_preview_click(self, event):
        for fixture_id, (x1, y1, x2, y2) in self.preview_bounds.items():
            if x1 <= event.x <= x2 and y1 <= event.y <= y2:
                fixture = next((item for item in self.show["fixtures"] if item["id"] == fixture_id), None)
                if not fixture:
                    return
                self.selected_ids = {fixture_id}
                self.group_filter.set("Все")
                self._refresh_fixture_list()
                return

    def _make_dmx_frame(self):
        slots = bytearray(512)
        if self.blackout_active:
            self.output.send_frame(bytes(slots))
            return
        for fixture in self.show["fixtures"]:
            address = int(fixture.get("address", 1))
            look = fixture.get("look", blank_look())
            dimmer = max(0, min(255, int(look.get("dimmer", 0))))
            for key in ("r", "g", "b", "w"):
                offset = int(fixture.get("offsets", {}).get(key, -1))
                channel = address + offset
                if 0 <= offset < SLOT_SIZE and 1 <= channel <= 512:
                    value = max(0, min(255, int(look.get(key, 0))))
                    slots[channel - 1] = round(value * dimmer / 255)
        self.output.send_frame(bytes(slots))

    def _refresh_patch_tree(self):
        if not self.patch_tree:
            return
        for item in self.patch_tree.get_children():
            self.patch_tree.delete(item)
        for fixture in self._ordered_fixtures():
            links = self._gang_name_for_fixture(fixture["id"])
            if fixture.get("mirror_group_id"):
                links = f"ЗЕРКАЛО · {links}" if links else "ЗЕРКАЛО"
            if fixture["id"] in self.gang_isolated_ids and links:
                links += " · ISO"
            self.patch_tree.insert("", "end", iid=fixture["id"], values=(
                fixture["name"], f"{int(fixture['address']):03d}", fixture["group"], "PAR RGBW · 4 канала", links
            ))

    def _load_patch_form(self, _event=None):
        selection = self.patch_tree.selection()
        if not selection:
            return
        fixture = next((x for x in self.show["fixtures"] if x["id"] == selection[0]), None)
        if not fixture:
            return
        self._editing_fixture = fixture["id"]
        self.patch_vars["name"].set(fixture["name"])
        self.patch_vars["address"].set(str(fixture["address"]))
        self.patch_vars["group"].set(fixture["group"])
        for key in ("r", "g", "b", "w"):
            self.patch_vars[key].set(str(int(fixture.get("offsets", {}).get(key, 0)) + 1))

    def apply_patch_form(self):
        fixture = next((x for x in self.show["fixtures"] if x["id"] == getattr(self, "_editing_fixture", None)), None)
        if not fixture:
            messagebox.showinfo("Патч", "Сначала выберите прибор в списке.")
            return
        try:
            address = int(self.patch_vars["address"].get())
            offsets = {key: int(self.patch_vars[key].get()) - 1 for key in ("r", "g", "b", "w")}
        except ValueError:
            messagebox.showerror("Патч", "Адрес и номера каналов должны быть числами.")
            return
        span = max(offsets.values()) + 1
        if not 1 <= address <= 512 or address + span - 1 > 512:
            messagebox.showerror("Патч", f"Для профиля на {span} канала начальный адрес должен быть от 1 до {513 - span}.")
            return
        if any(not 0 <= v < SLOT_SIZE for v in offsets.values()) or len(set(offsets.values())) < 4:
            messagebox.showerror("Патч", "RGBW должны занимать разные каналы от 1 до 16.")
            return
        new_channels = {address + offset for offset in offsets.values()}
        for other in self.show["fixtures"]:
            other_offsets = other.get("offsets", {"r": 0, "g": 1, "b": 2, "w": 3})
            same_mirror = fixture.get("mirror_group_id") and fixture.get("mirror_group_id") == other.get("mirror_group_id")
            other_channels = {other["address"] + offset for offset in other_offsets.values()}
            if other["id"] != fixture["id"] and not same_mirror and new_channels.intersection(other_channels):
                messagebox.showerror("Конфликт адресов", f"Профиль прибора пересекается с адресами {other['name']}.")
                return
        group = self.patch_vars["group"].get().strip() or "Сцена"
        if group not in self.show["groups"]:
            self.show["groups"].append(group)
        fixture["name"] = self.patch_vars["name"].get().strip() or fixture["name"]
        linked = [other for other in self.show["fixtures"]
                  if fixture.get("mirror_group_id") and other.get("mirror_group_id") == fixture.get("mirror_group_id")]
        for item in linked or [fixture]:
            item["address"] = address
            item["group"] = group
            item["offsets"] = copy.deepcopy(offsets)
        self.dirty = True
        self._refresh_all()

    def add_fixture(self):
        used_channels = {int(fixture["address"]) + int(offset)
                         for fixture in self.show["fixtures"]
                         for offset in fixture.get("offsets", {}).values()}
        offsets = {"r": 0, "g": 1, "b": 2, "w": 3}
        preferred = list(range(1, 498, SLOT_SIZE))
        candidates = preferred + [address for address in range(1, 510) if address not in preferred]
        addr = next((candidate for candidate in candidates
                     if candidate + 3 <= 512 and not any(candidate + offset in used_channels for offset in offsets.values())), None)
        if addr is None:
            messagebox.showerror("Патч", "В этой DMX-вселенной нет свободного места для нового PAR.")
            return
        fixture = {"id": uid(), "name": f"PAR {len(self.show['fixtures']) + 1:02d}", "address": addr,
                   "group": "Сцена", "offsets": offsets, "look": blank_look()}
        if "Сцена" not in self.show["groups"]:
            self.show["groups"].append("Сцена")
        self.show["fixtures"].append(fixture)
        self._editing_fixture = fixture["id"]
        self.dirty = True
        self._refresh_all()
        self.patch_tree.selection_set(fixture["id"])
        self._load_patch_form()

    def create_mirror_group(self):
        selected = self.patch_tree.selection()
        fixture = next((item for item in self.show["fixtures"] if selected and item["id"] == selected[0]), None)
        if not fixture:
            messagebox.showinfo("Зеркальная группа", "Выберите прибор в списке патча.")
            return
        count = simpledialog.askinteger("Зеркальная группа", "Сколько дополнительных прожекторов на этом же адресе?",
                                        initialvalue=1, minvalue=1, maxvalue=64, parent=self.root)
        if not count:
            return
        mirror_id = fixture.get("mirror_group_id") or uid()
        fixture["mirror_group_id"] = mirror_id
        existing = sum(1 for item in self.show["fixtures"] if item.get("mirror_group_id") == mirror_id)
        for index in range(count):
            clone = copy.deepcopy(fixture)
            clone["id"] = uid()
            clone["name"] = f"{fixture['name']} · {existing + index + 1}"
            clone["mirror_group_id"] = mirror_id
            self.show["fixtures"].append(clone)
            for scene in self.show.get("scenes", []):
                scene.setdefault("look", {})[clone["id"]] = copy.deepcopy(scene.get("look", {}).get(fixture["id"], fixture["look"]))
        self.dirty = True
        self._refresh_all()

    def remove_fixture(self):
        selected = self.patch_tree.selection()
        if not selected:
            return
        if not messagebox.askyesno("Удалить прибор", "Удалить выбранный прибор из шоу?"):
            return
        fixture_id = selected[0]
        self.show["fixtures"] = [f for f in self.show["fixtures"] if f["id"] != fixture_id]
        stage_objects = self.show.get("stage", {}).get("objects", [])
        self.show["stage"]["objects"] = [item for item in stage_objects if item.get("fixture_id") != fixture_id]
        for scene in self.show.get("scenes", []):
            scene.get("look", {}).pop(fixture_id, None)
        for gang in self.show.get("gangs", []):
            gang["members"] = [member for member in gang.get("members", []) if member != fixture_id]
        self.show["gangs"] = [gang for gang in self.show.get("gangs", []) if len(gang.get("members", [])) > 1]
        self.selected_ids.discard(fixture_id)
        self.dirty = True
        self._refresh_all()

    def auto_patch(self):
        mode = self.patch_step_var.get()
        if mode == "Ручной режим":
            self.status_var.set("Ручной режим патча · адреса не менялись")
            return
        try:
            step = int(self.patch_step_entry_var.get()) if mode == "Свой шаг…" else int(mode.split(" ·", 1)[0])
        except ValueError:
            messagebox.showerror("Автопатч", "Укажите целый шаг в каналах.")
            return
        if not 1 <= step <= 512:
            messagebox.showerror("Автопатч", "Шаг должен быть от 1 до 512 каналов.")
            return
        footprint = max((max(f.get("offsets", {}).values()) + 1 for f in self.show["fixtures"]), default=1)
        if step < footprint:
            messagebox.showerror("Автопатч", f"Шаг меньше профиля прибора ({footprint} канала) и создаст пересечение адресов.")
            return
        patch_units = []
        seen_mirrors = set()
        for fixture in self.show["fixtures"]:
            mirror_id = fixture.get("mirror_group_id")
            if mirror_id:
                if mirror_id in seen_mirrors:
                    continue
                seen_mirrors.add(mirror_id)
            patch_units.append(fixture)
        if patch_units and 1 + (len(patch_units) - 1) * step + footprint - 1 > 512:
            messagebox.showerror("Автопатч", "При выбранном шаге приборы не помещаются в одну DMX-вселенную.")
            return
        addresses = {}
        for idx, fixture in enumerate(patch_units):
            addresses[fixture.get("mirror_group_id") or fixture["id"]] = 1 + idx * step
        for fixture in self.show["fixtures"]:
            fixture["address"] = addresses.get(fixture.get("mirror_group_id") or fixture["id"], 1)
        self.dirty = True
        self._refresh_all()

    def store_scene(self):
        name = simpledialog.askstring("Сохранить сцену", "Название сцены:", initialvalue=f"Сцена {len(self.show['scenes']) + 1}", parent=self.root)
        if not name:
            return
        scene = {"id": uid(), "name": name.strip(), "look": {f["id"]: copy.deepcopy(f["look"]) for f in self.show["fixtures"]}}
        self.show["scenes"].append(scene)
        self.dirty = True
        self._refresh_scene_tree()
        self.scene_tree.selection_set(scene["id"])

    def store_scene_and_cue(self):
        name = simpledialog.askstring("Сцена и snapshot", "Название сцены:",
                                      initialvalue=f"Сцена {len(self.show['scenes']) + 1}", parent=self.root)
        if not name or not name.strip():
            return
        scene = {"id": uid(), "name": name.strip(),
                 "look": {fixture["id"]: copy.deepcopy(fixture["look"]) for fixture in self.show["fixtures"]}}
        self.show["scenes"].append(scene)
        self.dirty = True
        self._refresh_scene_tree()
        self.scene_tree.selection_set(scene["id"])
        if self._append_cue_for_scene(scene):
            self.status_var.set(f"СОЗДАНЫ СЦЕНА И SNAPSHOT · {scene['name']}")

    def add_selected_scene_to_cue(self):
        scene = self._selected_scene()
        if not scene:
            messagebox.showinfo("Snapshots", "Выберите сцену в консоли или сначала сохраните состояние.")
            return
        if self._append_cue_for_scene(scene):
            self.status_var.set(f"SNAPSHOT ДОБАВЛЕН · {scene['name']}")

    def _append_cue_for_scene(self, scene):
        try:
            fade = max(0.0, min(600.0, float(self.fade_var.get().replace(",", "."))))
        except ValueError:
            messagebox.showerror("Snapshots", "Время перехода должно быть числом секунд.")
            return False
        cue = {"id": uid(), "scene_id": scene["id"], "label": scene["name"], "fade": fade,
               "look": copy.deepcopy(scene.get("look", {}))}
        self.show["cues"].append(cue)
        self.dirty = True
        self._refresh_cues()
        self.cue_tree.selection_set(cue["id"])
        self._draw_next_cue_preview()
        return True

    def _selected_scene(self):
        selection = self.scene_tree.selection() if self.scene_tree else ()
        return next((x for x in self.show["scenes"] if selection and x["id"] == selection[0]), None)

    def recall_selected_scene(self):
        scene = self._selected_scene()
        if scene:
            self.current_cue = -1
            self._apply_scene(scene, 0.0)
            self._refresh_cues()

    def delete_selected_scene(self):
        scene = self._selected_scene()
        if not scene:
            return
        live_index = getattr(self, "current_cue", -1)
        live_id = self.show["cues"][live_index]["id"] if 0 <= live_index < len(self.show["cues"]) else None
        self.show["scenes"] = [s for s in self.show["scenes"] if s["id"] != scene["id"]]
        self.show["cues"] = [c for c in self.show["cues"] if c["scene_id"] != scene["id"]]
        self.current_cue = next((index for index, cue in enumerate(self.show["cues"]) if cue["id"] == live_id), -1)
        self.dirty = True
        self._refresh_all()

    def _refresh_scene_tree(self):
        if not self.scene_tree:
            return
        for item in self.scene_tree.get_children():
            self.scene_tree.delete(item)
        for scene in self.show["scenes"]:
            self.scene_tree.insert("", "end", iid=scene["id"], values=(scene["name"], len(scene["look"])))

    def add_cue(self):
        scene = self._selected_scene()
        if not scene:
            messagebox.showinfo("Cue-лист", "Сначала выберите сцену на вкладке «Пульт».")
            return
        if self._append_cue_for_scene(scene):
            self.tabs.select(self.cue_tab)

    def _edit_cue_cell(self, event):
        row_id = self.cue_tree.identify_row(event.y)
        column = self.cue_tree.identify_column(event.x)
        if not row_id or column not in ("#2", "#3", "#4"):
            return
        bounds = self.cue_tree.bbox(row_id, column)
        if not bounds:
            return
        cue = next((item for item in self.show["cues"] if item["id"] == row_id), None)
        if not cue:
            return
        x, y, width, height = bounds
        widget = None
        if column == "#3":
            names = [scene["name"] for scene in self.show["scenes"]]
            if not names:
                return
            widget = ttk.Combobox(self.cue_tree, values=names, state="readonly")
            current = next((scene["name"] for scene in self.show["scenes"] if scene["id"] == cue["scene_id"]), "")
            widget.set(current)
        else:
            widget = tk.Entry(self.cue_tree, bg=PANEL_2, fg=TEXT, insertbackground=TEXT, relief="flat")
            if column == "#2":
                widget.insert(0, cue.get("label", self._cue_scene_name(cue)))
            else:
                widget.insert(0, str(cue.get("fade", 0)))
        widget.place(x=x, y=y, width=width, height=height)
        widget.focus_set()
        if isinstance(widget, ttk.Combobox):
            widget.bind("<<ComboboxSelected>>", lambda _e: commit())

        def commit(_event=None):
            if not widget.winfo_exists():
                return
            value = widget.get().strip()
            if column == "#2" and value:
                cue["label"] = value
                self.dirty = True
            elif column == "#3":
                linked = next((scene for scene in self.show["scenes"] if scene["name"] == value), None)
                if linked:
                    cue["scene_id"] = linked["id"]
                    self.dirty = True
            elif column == "#4":
                try:
                    cue["fade"] = max(0.0, min(600.0, float(value.replace(",", "."))))
                    self.dirty = True
                except ValueError:
                    messagebox.showerror("Cue-лист", "Время перехода должно быть числом секунд.")
            widget.destroy()
            self._refresh_cues()
            if row_id in self.cue_tree.get_children():
                self.cue_tree.selection_set(row_id)

        widget.bind("<Return>", commit)
        widget.bind("<Escape>", lambda _e: widget.destroy())
        widget.bind("<FocusOut>", commit)

    def edit_selected_cue(self):
        selection = self.cue_tree.selection()
        if not selection:
            messagebox.showinfo("Настройки snapshot", "Сначала выберите snapshot в списке.", parent=self.root)
            return
        cue_id = selection[0]
        cue = next((item for item in self.show["cues"] if item["id"] == cue_id), None)
        if not cue:
            return
        scenes = self.show.get("scenes", [])
        if not scenes:
            messagebox.showinfo("Настройки snapshot", "В шоу нет сцен, которые можно назначить snapshot.", parent=self.root)
            return
        if self.cue_edit_overlay:
            old_bind_id = getattr(self.cue_edit_overlay, "outside_bind_id", None)
            if old_bind_id:
                try:
                    self.root._unbind(("bind", "all", "<ButtonPress-1>"), old_bind_id)
                except tk.TclError:
                    pass
            self.cue_edit_overlay.destroy()
        overlay = tk.Frame(self.cue_tab, bg=PANEL, highlightthickness=1, highlightbackground=LINE,
                           padx=20, pady=16, width=500, height=460)
        self.cue_edit_overlay = overlay
        overlay.pack_propagate(False)
        overlay.place(relx=0.5, rely=0.5, anchor="center", width=500, height=460)
        overlay.lift()
        title = tk.Label(overlay, text="НАСТРОЙКИ SNAPSHOT  ·  ПЕРЕТАЩИТЕ, ЧТОБЫ ПЕРЕМЕСТИТЬ",
                         bg=PANEL, fg=ACCENT, cursor="fleur", font=("Segoe UI Semibold", 10))
        title.pack(anchor="w", pady=(0, 12))
        self._bind_floating_panel(overlay, title)
        tk.Label(overlay, text="ИМЯ SNAPSHOT", bg=PANEL, fg=MUTED,
                 font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(0, 4))
        name_var = tk.StringVar(value=cue.get("label", self._cue_scene_name(cue)))
        name_entry = tk.Entry(overlay, textvariable=name_var, bg=PANEL_2, fg=TEXT,
                              insertbackground=TEXT, relief="flat", width=36)
        name_entry.pack(fill="x", ipady=6, pady=(0, 12))
        tk.Label(overlay, text="СЦЕНА", bg=PANEL, fg=MUTED,
                 font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(0, 4))
        scene_names = [scene["name"] for scene in scenes]
        scene_var = tk.StringVar()
        scene_box = ttk.Combobox(overlay, textvariable=scene_var, values=scene_names, state="readonly", width=34)
        current_scene_index = next((i for i, scene in enumerate(scenes) if scene["id"] == cue.get("scene_id")), 0)
        scene_box.current(current_scene_index)
        if not scene_var.get() and scene_names:
            scene_box.set(scene_names[current_scene_index])
        scene_box.pack(fill="x", ipady=3, pady=(0, 12))
        tk.Label(overlay, text="ПЕРЕХОД (СЕК.)", bg=PANEL, fg=MUTED,
                 font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(0, 4))
        fade_var = tk.StringVar(value=str(cue.get("fade", 0)))
        fade_entry = tk.Entry(overlay, textvariable=fade_var, bg=PANEL_2, fg=TEXT,
                              insertbackground=TEXT, relief="flat", width=12)
        fade_entry.pack(anchor="w", ipady=6)
        method_names = {"manual": "Manual update", "auto": "Auto Update", "group": "Group update",
                        "relative": "Relative group", "absolute": "Absolute group"}
        method_var = tk.StringVar(value=cue.get("update_method", "manual"))
        tk.Label(overlay, text="UPDATE METHOD", bg=PANEL, fg=MUTED,
                 font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(12, 4))
        method_box = ttk.Combobox(overlay, textvariable=method_var, values=list(method_names.values()), state="readonly")
        method_box.current(list(method_names).index(method_var.get()) if method_var.get() in method_names else 0)
        method_box.pack(fill="x", ipady=3)
        tk.Label(overlay, text="КАНАЛЫ, КОТОРЫЕ ОБНОВЛЯЕТ SNAPSHOT", bg=PANEL, fg=MUTED,
                 font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(12, 4))
        channel_vars = {}
        channel_row = tk.Frame(overlay, bg=PANEL)
        channel_row.pack(fill="x")
        for channel in ("dimmer", "r", "g", "b", "w"):
            var = tk.BooleanVar(value=channel in cue.get("update_channels", ["dimmer", "r", "g", "b", "w"]))
            channel_vars[channel] = var
            tk.Checkbutton(channel_row, text=channel.upper(), variable=var, bg=PANEL, fg=TEXT,
                           selectcolor=PANEL_2, activebackground=PANEL, activeforeground=TEXT).pack(side="left", padx=(0, 8))
        fixture_ids = [fixture["id"] for fixture in self.show.get("fixtures", [])]
        update_fixtures = cue.get("update_fixtures", fixture_ids)
        all_fixtures_var = tk.BooleanVar(value=set(update_fixtures) >= set(fixture_ids))
        tk.Checkbutton(overlay, text="Обновлять все приборы (иначе — только выбранные сейчас)",
                       variable=all_fixtures_var, bg=PANEL, fg=TEXT, selectcolor=PANEL_2,
                       activebackground=PANEL, activeforeground=TEXT).pack(anchor="w", pady=(8, 0))
        buttons = tk.Frame(overlay, bg=PANEL)
        buttons.pack(side="bottom", fill="x", pady=(18, 0))

        def save_changes():
            label = name_var.get().strip()
            try:
                fade = float(fade_var.get().strip().replace(",", "."))
            except ValueError:
                messagebox.showerror("Snapshot", "Время перехода должно быть числом секунд.", parent=self.root)
                return
            if not 0 <= fade <= 600:
                messagebox.showerror("Snapshot", "Время перехода должно быть от 0 до 600 секунд.", parent=self.root)
                return
            scene_index = scene_box.current()
            selected_scene = scenes[scene_index] if 0 <= scene_index < len(scenes) else None
            if selected_scene is None:
                selected_scene = next((scene for scene in scenes if scene["name"] == scene_var.get()), None)
            if selected_scene is None:
                selected_scene = next((scene for scene in scenes if scene["id"] == cue.get("scene_id")), scenes[0])
            if cue.get("scene_id") != selected_scene["id"]:
                cue["look"] = copy.deepcopy(selected_scene.get("look", {}))
            cue["label"] = label or selected_scene["name"]
            cue["scene_id"] = selected_scene["id"]
            cue["fade"] = fade
            cue["update_method"] = next((key for key, value in method_names.items() if value == method_var.get()), "manual")
            cue["update_channels"] = [key for key, var in channel_vars.items() if var.get()]
            if all_fixtures_var.get():
                cue["update_fixtures"] = fixture_ids
            else:
                cue["update_fixtures"] = [fixture["id"] for fixture in self._selected_fixtures()]
            self.dirty = True
            close_editor()
            self._refresh_cues()
            self.cue_tree.selection_set(cue_id)
            self.cue_tree.focus(cue_id)
            self._draw_next_cue_preview()

        def close_editor():
            if getattr(overlay, "outside_bind_id", None):
                try:
                    self.root._unbind(("bind", "all", "<ButtonPress-1>"), overlay.outside_bind_id)
                except tk.TclError:
                    pass
            overlay.destroy()
            self.cue_edit_overlay = None

        def outside_click(event):
            if not overlay.winfo_exists():
                return
            widget = event.widget
            while widget is not None:
                if widget is overlay:
                    return
                widget = getattr(widget, "master", None)
            save_changes()

        self._button(buttons, "Отмена", close_editor, small=True).pack(side="right", padx=(6, 0))
        self._button(buttons, "Сохранить", save_changes, primary=True, small=True).pack(side="right")
        overlay.bind("<Escape>", lambda _event: close_editor())
        name_entry.bind("<Return>", lambda _event: save_changes())
        name_entry.bind("<Escape>", lambda _event: close_editor())
        scene_box.bind("<Escape>", lambda _event: close_editor())
        fade_entry.bind("<Return>", lambda _event: save_changes())
        fade_entry.bind("<Escape>", lambda _event: close_editor())
        overlay.outside_bind_id = self.root.bind_all("<ButtonPress-1>", outside_click, add="+")
        name_entry.focus_set()
        name_entry.selection_range(0, "end")

    def remove_cue(self):
        selection = self.cue_tree.selection()
        if not selection:
            return
        live_index = getattr(self, "current_cue", -1)
        live_id = self.show["cues"][live_index]["id"] if 0 <= live_index < len(self.show["cues"]) else None
        selected_ids = set(selection)
        self.show["cues"] = [cue for cue in self.show["cues"] if cue["id"] not in selected_ids]
        self.current_cue = next((index for index, cue in enumerate(self.show["cues"]) if cue["id"] == live_id), -1)
        self.dirty = True
        self._refresh_cues()

    def move_cue(self, direction):
        selection = self.cue_tree.selection()
        if not selection:
            return
        index = self.cue_tree.index(selection[0])
        target = index + direction
        if not 0 <= target < len(self.show["cues"]):
            return
        cues = self.show["cues"]
        live_index = getattr(self, "current_cue", -1)
        live_id = cues[live_index]["id"] if 0 <= live_index < len(cues) else None
        cues[index], cues[target] = cues[target], cues[index]
        self.current_cue = next((position for position, cue in enumerate(cues) if cue["id"] == live_id), -1)
        self.dirty = True
        self._refresh_cues()
        self.cue_tree.selection_set(self.cue_tree.get_children()[target])

    def _refresh_cues(self):
        if not self.cue_tree:
            return
        for item in self.cue_tree.get_children():
            self.cue_tree.delete(item)
        for index, cue in enumerate(self.show["cues"], start=1):
            scene = next((s for s in self.show["scenes"] if s["id"] == cue["scene_id"]), None)
            scene_name = scene["name"] if scene else "[сцена не найдена]"
            label = cue.get("label", scene_name)
            state = "ТЕКУЩИЙ" if index - 1 == getattr(self, "current_cue", -1) else "ГОТОВ"
            self.cue_tree.insert("", "end", iid=cue["id"], values=(f"{index:02d}", label, scene_name, f"{cue['fade']:.1f} с", state))
        self._update_live_snapshot_label()
        self._draw_next_cue_preview()

    def _draw_next_cue_preview(self):
        if not getattr(self, "next_scene_canvas", None):
            return
        current_index = getattr(self, "current_cue", -1)
        current_preview = {"name": "Сейчас на сцене",
                           "look": {fixture["id"]: copy.deepcopy(fixture["look"])
                                    for fixture in self.show.get("fixtures", [])}}
        current_is_live = True
        live_index = getattr(self, "current_cue", -1)
        live_cues = self.show.get("cues", [])
        if 0 <= live_index < len(live_cues):
            live_cue = live_cues[live_index]
            live_scene = next((item for item in self.show.get("scenes", []) if item["id"] == live_cue.get("scene_id")), None)
            current_label = f"LIVE · SNAPSHOT {live_index + 1:02d} · {live_cue.get('label', live_scene.get('name', '') if live_scene else '')}"
        else:
            current_label = "LIVE · РУЧНОЕ СОСТОЯНИЕ · SNAPSHOT НЕ ВЫЗВАН"
        if self.space_preview_active:
            cue_id = self.hovered_cue_id or self._cue_at_pointer()
            if not cue_id:
                selected = self.cue_tree.selection()
                cue_id = selected[0] if selected else None
            preview_cue = next((cue for cue in self.show.get("cues", []) if cue["id"] == cue_id), None)
            if preview_cue:
                linked_scene = next((scene for scene in self.show.get("scenes", [])
                                     if scene["id"] == preview_cue.get("scene_id")), None)
                current_preview = ({**linked_scene, "look": preview_cue.get("look", linked_scene.get("look", {}))}
                                   if linked_scene else None)
                if current_preview:
                    current_is_live = False
                    cue_index = next((i for i, cue in enumerate(self.show["cues"]) if cue["id"] == cue_id), 0)
                    current_label = f"ПРЕДПРОСМОТР · SNAPSHOT {cue_index + 1:02d} · {preview_cue.get('label', current_preview['name'])}"
        self.current_scene_label.configure(text=current_label)
        self._render_cue_scene(self.current_scene_canvas, current_preview, actual=current_is_live)

        next_index = current_index + 1
        selected = self.cue_tree.selection() if getattr(self, "cue_tree", None) else ()
        if selected and selected[0] in self.cue_tree.get_children():
            selected_index = self.cue_tree.index(selected[0])
            if selected_index != current_index:
                next_index = selected_index
        next_scene = None
        next_cue = None
        if 0 <= next_index < len(self.show.get("cues", [])):
            next_cue = self.show["cues"][next_index]
            next_scene = next((scene for scene in self.show.get("scenes", [])
                               if scene["id"] == next_cue.get("scene_id")), None)
        if next_scene and next_cue:
            self.next_scene_label.configure(text=f"СЛЕДУЮЩАЯ · {next_index + 1:02d} · {next_cue.get('label', next_scene['name'])}  ·  {next_scene['name']}  ·  переход {next_cue.get('fade', 0):.1f} с")
        else:
            self.next_scene_label.configure(text="СЛЕДУЮЩАЯ СЦЕНА · snapshot не выбран")
        if next_cue and next_scene:
            next_scene = {**next_scene, "look": next_cue.get("look", next_scene.get("look", {}))}
        self._render_cue_scene(self.next_scene_canvas, next_scene)

    def _render_cue_scene(self, canvas, scene, actual=False):
        if not scene:
            canvas.delete("all")
            canvas.create_text(12, 20, text="Нет сцены для предпросмотра", anchor="nw", fill=MUTED,
                               font=("Segoe UI", 9))
            return
        self._render_stage(canvas, look_override=scene.get("look", {}), actual=actual)

    def _cue_at_pointer(self):
        if not getattr(self, "cue_tree", None):
            return None
        pointer_x, pointer_y = self.root.winfo_pointerxy()
        left, top = self.cue_tree.winfo_rootx(), self.cue_tree.winfo_rooty()
        if left <= pointer_x < left + self.cue_tree.winfo_width() and top <= pointer_y < top + self.cue_tree.winfo_height():
            return self.cue_tree.identify_row(pointer_y - top) or None
        return None

    def _on_cue_hover(self, event):
        self.hovered_cue_id = self.cue_tree.identify_row(event.y) or None
        if self.space_preview_active:
            self._draw_next_cue_preview()

    def _on_cue_leave(self, _event=None):
        self.hovered_cue_id = None
        if self.space_preview_active:
            self._draw_next_cue_preview()

    def _space_preview_press(self, _event=None):
        if self._cue_at_pointer() is None and self.root.focus_get() is not self.cue_tree:
            return None
        if not (self.hovered_cue_id or self._cue_at_pointer() or self.cue_tree.selection()):
            return None
        self.space_preview_active = True
        self._draw_next_cue_preview()
        return "break"

    def _space_preview_release(self, _event=None):
        if not self.space_preview_active:
            return None
        self.space_preview_active = False
        self._draw_next_cue_preview()
        return "break"

    def fire_selected_snapshot(self):
        selection = self.cue_tree.selection()
        if selection:
            self._call_cue(selection[0])

    def recall_selected_snapshot(self):
        selection = self.cue_tree.selection()
        if not selection:
            return
        cue = next((item for item in self.show["cues"] if item["id"] == selection[0]), None)
        scene = next((item for item in self.show["scenes"] if cue and item["id"] == cue.get("scene_id")), None)
        if scene:
            self.current_cue = self.show["cues"].index(cue)
            scene = {**scene, "look": cue.get("look", scene.get("look", {}))}
            self._apply_scene(scene, 0, f"RECALL · {cue.get('label', scene['name'])}")
            self.cue_status.configure(text=f"Recall · {cue.get('label', scene['name'])}")
            self._refresh_cues()
            self.cue_tree.selection_set(cue["id"])

    def open_snapshot_update_menu(self):
        menu = tk.Menu(self.root, tearoff=False, bg=PANEL, fg=TEXT, activebackground=ACCENT,
                       activeforeground="#10151b", font=("Segoe UI", 9))
        methods = [("Manual update", "manual"), ("Auto Update", "auto"), ("Group update", "group"),
                   ("Relative group", "relative"), ("Absolute group", "absolute")]
        for label, method in methods:
            menu.add_command(label=label, command=lambda m=method: self.configure_snapshot_update(m))
        menu.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())

    def configure_snapshot_update(self, method):
        selected = list(self.cue_tree.selection())
        if not selected:
            messagebox.showinfo("Snapshot update", "Выберите один или несколько snapshots.", parent=self.root)
            return
        snapshots = [item for item in self.show["cues"] if item["id"] in selected]
        first = snapshots[0]
        channels = ("dimmer", "r", "g", "b", "w")
        channel_vars = {key: tk.BooleanVar(value=key in first.get("update_channels", channels)) for key in channels}
        dialog = tk.Toplevel(self.root)
        dialog.title(dict(manual="Manual update", auto="Auto Update", group="Group update",
                          relative="Relative group", absolute="Absolute group")[method])
        dialog.configure(bg=PANEL)
        dialog.transient(self.root)
        dialog.resizable(False, False)
        box = tk.Frame(dialog, bg=PANEL, padx=18, pady=16)
        box.pack(fill="both", expand=True)
        tk.Label(box, text=dialog.title().upper(), bg=PANEL, fg=ACCENT,
                 font=("Segoe UI Semibold", 11)).pack(anchor="w")
        tk.Label(box, text="Какие каналы обновлять из текущего состояния пульта?", bg=PANEL, fg=MUTED,
                 font=("Segoe UI", 9)).pack(anchor="w", pady=(6, 8))
        row = tk.Frame(box, bg=PANEL)
        row.pack(anchor="w")
        for key, var in channel_vars.items():
            tk.Checkbutton(row, text=key.upper(), variable=var, bg=PANEL, fg=TEXT,
                           selectcolor=PANEL_2, activebackground=PANEL, activeforeground=TEXT).pack(side="left", padx=(0, 8))
        target_var = tk.StringVar(value="selected" if len(selected) > 1 else "one")
        if method in ("group", "relative", "absolute"):
            tk.Label(box, text="ГРУППА SNAPSHOTS", bg=PANEL, fg=MUTED,
                     font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(12, 4))
            target_box = ttk.Combobox(box, textvariable=target_var,
                                      values=("selected", "all"), state="readonly", width=20)
            target_box.pack(anchor="w")
            target_box.set("selected")
            tk.Label(box, text="selected — выбранные строки · all — весь список", bg=PANEL, fg=MUTED,
                     font=("Segoe UI", 8)).pack(anchor="w", pady=(3, 0))
            if method == "group":
                tk.Label(box, text="Group update переносит разницу текущего света относительно первого выбранного snapshot на всю группу.",
                         bg=PANEL, fg=MUTED, wraplength=360, justify="left", font=("Segoe UI", 8)).pack(anchor="w", pady=(8, 0))
            elif method == "absolute":
                tk.Label(box, text="Absolute group записывает одинаковые текущие значения во все snapshots группы.",
                         bg=PANEL, fg=MUTED, wraplength=360, justify="left", font=("Segoe UI", 8)).pack(anchor="w", pady=(8, 0))
            elif method == "relative":
                tk.Label(box, text="Relative group прибавляет к snapshots разницу между текущим светом и выбранной опорой.",
                         bg=PANEL, fg=MUTED, wraplength=360, justify="left", font=("Segoe UI", 8)).pack(anchor="w", pady=(8, 0))
        ref_var = tk.StringVar(value=first.get("label", self._cue_scene_name(first)))
        if method == "relative":
            tk.Label(box, text="ОТНОСИТЕЛЬНАЯ ОПОРА", bg=PANEL, fg=MUTED,
                     font=("Segoe UI Semibold", 8)).pack(anchor="w", pady=(12, 4))
            refs = [cue.get("label", self._cue_scene_name(cue)) for cue in self.show["cues"]]
            ref_box = ttk.Combobox(box, textvariable=ref_var, values=refs, state="readonly", width=32)
            ref_box.pack(anchor="w")
        if method == "auto":
            tk.Label(box, text="Auto Update будет записывать изменения пульта в выбранный snapshot после каждого движения фейдера/цвета.",
                     bg=PANEL, fg=MUTED, wraplength=360, justify="left", font=("Segoe UI", 8)).pack(anchor="w", pady=(10, 0))

        def apply_update():
            selected_channels = [key for key, var in channel_vars.items() if var.get()]
            if not selected_channels:
                messagebox.showinfo("Snapshot update", "Выберите хотя бы один канал.", parent=dialog)
                return
            targets = snapshots
            if method in ("group", "relative", "absolute") and target_var.get() == "all":
                targets = list(self.show["cues"])
            reference = next((cue for cue in self.show["cues"]
                              if cue.get("label", self._cue_scene_name(cue)) == ref_var.get()), first)
            current = {fixture["id"]: fixture["look"] for fixture in self.show["fixtures"]}
            base = reference.get("look") or next((scene for scene in self.show["scenes"] if scene["id"] == reference.get("scene_id")), {}).get("look", {})
            for cue in targets:
                if not cue.get("look"):
                    linked_scene = next((item for item in self.show["scenes"] if item["id"] == cue.get("scene_id")), None)
                    cue["look"] = copy.deepcopy(linked_scene.get("look", {}) if linked_scene else {})
                scope = set(cue.get("update_fixtures", [])) or {fixture["id"] for fixture in self.show["fixtures"]}
                for fixture in self.show["fixtures"]:
                    fixture_id = fixture["id"]
                    if fixture_id not in scope:
                        continue
                    scene_look = cue.setdefault("look", {}).setdefault(fixture_id, blank_look())
                    for channel in selected_channels:
                        live_value = current[fixture_id].get(channel, 0)
                        if method in ("relative", "group"):
                            reference_value = base.get(fixture_id, blank_look()).get(channel, 0)
                            scene_look[channel] = max(0, min(255, scene_look.get(channel, 0) + live_value - reference_value))
                        else:
                            scene_look[channel] = live_value
                cue["update_method"] = method
                cue["update_channels"] = selected_channels
                cue["update_group"] = [item["id"] for item in targets]
            self.dirty = True
            dialog.destroy()
            self._refresh_cues()

        buttons = tk.Frame(box, bg=PANEL)
        buttons.pack(fill="x", pady=(16, 0))
        self._button(buttons, "Отмена", dialog.destroy, small=True).pack(side="right", padx=(6, 0))
        self._button(buttons, "Применить UPDATE", apply_update, primary=True, small=True).pack(side="right")
        dialog.update_idletasks()
        dialog.geometry(f"+{self.root.winfo_rootx() + 160}+{self.root.winfo_rooty() + 120}")

    def _cue_scene_name(self, cue):
        scene = next((s for s in self.show["scenes"] if s["id"] == cue.get("scene_id")), None)
        return scene["name"] if scene else ""

    def go_cue(self):
        selection = self.cue_tree.selection()
        if selection:
            index = self.cue_tree.index(selection[0])
            if index == getattr(self, "current_cue", -1):
                index += 1
        else:
            index = getattr(self, "current_cue", -1) + 1
        if not self.show["cues"]:
            messagebox.showinfo("Snapshots", "Сначала добавьте сцены в список snapshots.")
            return
        if index >= len(self.show["cues"]):
            self.cue_status.configure(text="Конец списка snapshots")
            return
        index = max(0, index)
        self._call_cue(self.show["cues"][index]["id"])

    def _call_cue(self, cue_id):
        index = next((i for i, item in enumerate(self.show["cues"]) if item["id"] == cue_id), None)
        if index is None:
            return
        cue = self.show["cues"][index]
        scene = next((s for s in self.show["scenes"] if s["id"] == cue["scene_id"]), None)
        if not scene:
            return
        scene = {**scene, "look": cue.get("look", scene.get("look", {}))}
        self.current_cue = index
        self._apply_scene(scene, cue["fade"], f"ПЕРЕХОД · SNAPSHOT {index + 1:02d} · {cue.get('label', scene['name'])}")
        self.cue_status.configure(text=f"FIRE · {index + 1:02d} · {cue.get('label', scene['name'])}")
        self._refresh_cues()
        preview_index = index
        if self.auto_preview_next_var.get() and index + 1 < len(self.show["cues"]):
            preview_index = index + 1
        preview_id = self.show["cues"][preview_index]["id"]
        self.cue_tree.selection_set(preview_id)
        self.cue_tree.focus(preview_id)
        self.cue_tree.see(preview_id)
        self._draw_next_cue_preview()

    def previous_cue(self):
        if not self.show["cues"]:
            return
        index = max(0, getattr(self, "current_cue", 0) - 1)
        cue = self.show["cues"][index]
        scene = next((s for s in self.show["scenes"] if s["id"] == cue["scene_id"]), None)
        if scene:
            self.current_cue = index
            self._apply_scene(scene, cue["fade"], f"ПЕРЕХОД · CUE {index + 1:02d} · {cue.get('label', scene['name'])}")
            self.cue_status.configure(text=f"Вызвано {index + 1:02d} · {cue.get('label', scene['name'])}")
            self._refresh_cues()
            self.cue_tree.selection_set(cue["id"])

    def _apply_scene(self, scene, fade, transition_label="ПЕРЕХОД СЦЕНЫ"):
        targets = scene.get("look", {})
        start = {f["id"]: copy.deepcopy(f["look"]) for f in self.show["fixtures"]}
        end = {f["id"]: copy.deepcopy(targets.get(f["id"], blank_look())) for f in self.show["fixtures"]}
        if fade <= 0:
            for fixture in self.show["fixtures"]:
                fixture["look"] = end[fixture["id"]]
            self._fade = None
        else:
            self._fade = {"started": time.monotonic(), "duration": fade, "start": start, "end": end,
                          "label": transition_label}
        self.dirty = True
        self._sync_programmer()
        self._draw_preview()
        self._draw_next_cue_preview()
        self._make_dmx_frame()

    def blackout(self):
        self.blackout_active = not self.blackout_active
        if self.blackout_active:
            self.blackout_button.configure(text="ВОССТАНОВИТЬ СВЕТ", bg="#5a2430", fg="#ffdbe0")
            self.status_var.set("BLACKOUT ВКЛЮЧЁН · нажмите ещё раз, чтобы восстановить предыдущий свет")
        else:
            self.blackout_button.configure(text="ЗАТЕМНЕНИЕ", bg=PANEL_2, fg=TEXT)
            self.status_var.set("СВЕТ ВОССТАНОВЛЕН · значения программатора не изменялись")
        self._draw_preview()
        self._draw_next_cue_preview()
        self._make_dmx_frame()

    def _tick(self):
        if self._fade:
            now = time.monotonic()
            amount = min(1.0, (now - self._fade["started"]) / self._fade["duration"])
            ease = amount * amount * (3 - 2 * amount)
            for fixture in self.show["fixtures"]:
                fid = fixture["id"]
                a = self._fade["start"].get(fid, blank_look())
                b = self._fade["end"].get(fid, blank_look())
                fixture["look"] = {k: round(a.get(k, 0) + (b.get(k, 0) - a.get(k, 0)) * ease) for k in ("dimmer", "r", "g", "b", "w")}
            if amount >= 1:
                self._fade = None
            self._draw_preview()
            self._draw_next_cue_preview()
            self._make_dmx_frame()
            self._sync_programmer()
        if self.output.error:
            error = self.output.error
            self.output.disconnect()
            self.status_dot.configure(fg=RED)
            self.status_var.set(f"ОШИБКА DMX · {error}")
            self.connect_button.configure(text="Подключить DMX")
        self.root.after(33, self._tick)

    def new_show(self):
        if not self._confirm_unsaved_action("Новое шоу"):
            return
        self._undo_stack.clear()
        self._redo_stack.clear()
        self._app_clipboard = None
        self._update_history_buttons()
        self.show = default_show()
        self.gang_isolated_ids.clear()
        self.file_path = None
        self.selected_ids = {self.show["fixtures"][0]["id"]}
        self.current_cue = -1
        self.group_filter.set("Все")
        self._fade = None
        self.dirty = False
        self.blackout_active = False
        self.blackout_button.configure(text="ЗАТЕМНЕНИЕ", bg=PANEL_2, fg=TEXT)
        self.status_var.set("ОФЛАЙН-РЕЖИМ · новое локальное шоу")
        self._refresh_all()

    def open_show(self):
        if not self._confirm_unsaved_action("Открыть другое шоу"):
            return
        path = filedialog.askopenfilename(title="Открыть шоу OLEG", filetypes=[("Шоу OLEG", "*.dmxshow *.json"), ("Все файлы", "*.*")])
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as stream:
                data = json.load(stream)
            self._migrate_show_data(data)
            self._validate_show_data(data)
            self._undo_stack.clear()
            self._redo_stack.clear()
            self._app_clipboard = None
            self._update_history_buttons()
            self.show = data
            self.gang_isolated_ids.clear()
            self.file_path = Path(path)
            self.selected_ids = {data["fixtures"][0]["id"]} if data["fixtures"] else set()
            self.current_cue = -1
            self.group_filter.set("Все")
            self._fade = None
            self.dirty = False
            self.blackout_active = False
            self.blackout_button.configure(text="ЗАТЕМНЕНИЕ", bg=PANEL_2, fg=TEXT)
            self.status_var.set(f"ОТКРЫТО · {self.file_path.name} · локальное шоу")
            self._refresh_all()
        except Exception as exc:
            messagebox.showerror("Открыть шоу", f"Не удалось открыть шоу:\n{exc}")

    def _confirm_unsaved_action(self, action):
        if not self.dirty:
            return True
        choice = messagebox.askyesnocancel(action, "Сохранить изменения перед продолжением?\n\nДа — сохранить · Нет — не сохранять · Отмена — остаться в шоу")
        if choice is None:
            return False
        if choice:
            self.save_show()
            return not self.dirty
        return True

    def _migrate_show_data(self, data):
        if not isinstance(data, dict) or data.get("format") != "luma-dmx-show":
            raise ValueError("Это не корректный файл шоу OLEG DMX.")
        version = data.get("format_version", 1)
        if version not in (0, 1):
            raise ValueError(f"Версия файла шоу {version} не поддерживается этой сборкой.")
        data["format_version"] = 1
        data.setdefault("name", "Новое шоу")
        data.setdefault("groups", ["Все", *DEFAULT_GROUPS])
        data.setdefault("scenes", [])
        data.setdefault("cues", [])
        data.setdefault("gangs", [])
        data.setdefault("stage", {"width_m": 8, "depth_m": 6, "objects": []})
        if not isinstance(data["fixtures"], list):
            raise ValueError("В файле шоу отсутствует корректный список приборов.")
        if any(not isinstance(data[key], list) for key in ("groups", "scenes", "cues", "gangs")):
            raise ValueError("В файле шоу повреждён список групп, сцен, cues или GANG.")
        group_names = {"All": "Все", "Front": "Передний план", "Stage": "Сцена", "Back": "Задник"}
        data["groups"] = [group_names.get(group, group) if isinstance(group, str) else group for group in data["groups"]]
        for index, fixture in enumerate(data["fixtures"], start=1):
            if not isinstance(fixture, dict):
                continue
            fixture.setdefault("name", f"PAR {index:02d}")
            fixture.setdefault("group", "Stage")
            fixture["group"] = group_names.get(fixture["group"], fixture["group"])
            fixture.setdefault("offsets", {"r": 0, "g": 1, "b": 2, "w": 3})
            fixture.setdefault("look", blank_look())
        for index, scene in enumerate(data["scenes"], start=1):
            if not isinstance(scene, dict):
                continue
            scene.setdefault("name", f"Сцена {index}")
            scene.setdefault("look", {})
        for cue in data["cues"]:
            if not isinstance(cue, dict):
                continue
            scene = next((item for item in data["scenes"]
                          if isinstance(item, dict) and item.get("id") == cue.get("scene_id")), None)
            cue.setdefault("label", scene.get("name", "Snapshot") if scene else "Snapshot")
            cue.setdefault("fade", 0.0)
            cue.setdefault("look", copy.deepcopy(scene.get("look", {}) if scene else {}))
            cue.setdefault("update_method", "manual")
            cue.setdefault("update_channels", ["dimmer", "r", "g", "b", "w"])
            cue.setdefault("update_fixtures", [fixture.get("id") for fixture in data["fixtures"] if isinstance(fixture, dict)])
            cue.setdefault("update_group", [])
        if data.get("name") == "Untitled Show":
            data["name"] = "Новое шоу"

    def _validate_show_data(self, data):
        if not isinstance(data, dict) or data.get("format") != "luma-dmx-show" or not isinstance(data.get("fixtures"), list):
            raise ValueError("Это не корректный файл шоу OLEG DMX.")
        fixture_ids = set()
        footprints = []
        for fixture in data["fixtures"]:
            if not isinstance(fixture, dict) or not isinstance(fixture.get("id"), str):
                raise ValueError("В списке патча найден прибор без корректного ID.")
            if fixture["id"] in fixture_ids:
                raise ValueError(f"ID прибора {fixture['id']} повторяется.")
            fixture_ids.add(fixture["id"])
            address = fixture.get("address")
            offsets = fixture.get("offsets", {"r": 0, "g": 1, "b": 2, "w": 3})
            if not isinstance(address, int) or not 1 <= address <= 512 or not isinstance(offsets, dict):
                raise ValueError(f"У прибора {fixture.get('name', fixture['id'])} неверный адрес или профиль.")
            normalized = {key: offsets.get(key, default) for key, default in (("r", 0), ("g", 1), ("b", 2), ("w", 3))}
            if any(not isinstance(offset, int) or not 0 <= offset < SLOT_SIZE for offset in normalized.values()):
                raise ValueError(f"У прибора {fixture.get('name', fixture['id'])} номер канала должен быть от 1 до {SLOT_SIZE}.")
            if len(set(normalized.values())) != 4 or address + max(normalized.values()) > 512:
                raise ValueError(f"Профиль прибора {fixture.get('name', fixture['id'])} выходит за границы вселенной или содержит повтор каналов.")
            fixture["offsets"] = normalized
            fixture.setdefault("look", blank_look())
            if not isinstance(fixture["look"], dict):
                raise ValueError(f"У прибора {fixture.get('name', fixture['id'])} повреждены значения света.")
            for key in ("dimmer", "r", "g", "b", "w"):
                value = fixture["look"].get(key, 0)
                if not isinstance(value, (int, float)) or not math.isfinite(value) or not 0 <= value <= 255:
                    raise ValueError(f"У прибора {fixture.get('name', fixture['id'])} значение канала {key.upper()} должно быть от 0 до 255.")
            footprints.append((fixture, {address + offset for offset in normalized.values()}))
        shared_profiles = {}
        for fixture, _channels in footprints:
            signature = (fixture["address"], tuple(sorted(fixture["offsets"].items())))
            shared_profiles.setdefault(signature, []).append(fixture)
        for members in shared_profiles.values():
            if len(members) > 1:
                mirror_ids = {member.get("mirror_group_id") for member in members if member.get("mirror_group_id")}
                if len(mirror_ids) > 1:
                    raise ValueError("Один и тот же DMX-адрес назначен нескольким разным зеркальным группам.")
                shared_id = next(iter(mirror_ids), None) or uid()
                for member in members:
                    member["mirror_group_id"] = shared_id
        mirror_profiles = {}
        for fixture, _channels in footprints:
            mirror_id = fixture.get("mirror_group_id")
            if mirror_id:
                profile = (fixture["address"], tuple(sorted(fixture["offsets"].items())))
                if mirror_id in mirror_profiles and mirror_profiles[mirror_id] != profile:
                    raise ValueError(f"Зеркальная группа прибора {fixture.get('name', fixture['id'])} содержит разные адреса или профили.")
                mirror_profiles[mirror_id] = profile
        for index, (fixture, channels) in enumerate(footprints):
            for other, other_channels in footprints[index + 1:]:
                same_mirror = fixture.get("mirror_group_id") and fixture.get("mirror_group_id") == other.get("mirror_group_id")
                exact_shared = fixture["address"] == other["address"] and fixture.get("offsets") == other.get("offsets")
                if channels.intersection(other_channels) and not same_mirror and not exact_shared:
                    raise ValueError(f"Патч приборов {fixture.get('name', fixture['id'])} и {other.get('name', other['id'])} пересекается. Совместный адрес создайте как зеркальную группу.")
                if same_mirror and (fixture["address"] != other["address"] or fixture.get("offsets") != other.get("offsets")):
                    raise ValueError(f"Приборы зеркальной группы {fixture.get('name', fixture['id'])} должны иметь одинаковые адрес и профиль.")
        data.setdefault("groups", ["Все"])
        data.setdefault("scenes", [])
        data.setdefault("cues", [])
        data.setdefault("gangs", [])
        if not isinstance(data["scenes"], list) or not isinstance(data["cues"], list) or not isinstance(data["gangs"], list):
            raise ValueError("Списки сцен, cues и GANG должны быть массивами.")
        if not isinstance(data.get("stage"), dict):
            data["stage"] = {"width_m": 8, "depth_m": 6, "objects": []}
        stage = data["stage"]
        stage.setdefault("width_m", 8); stage.setdefault("depth_m", 6); stage.setdefault("objects", [])
        if (not isinstance(stage["width_m"], int) or not 1 <= stage["width_m"] <= 100 or
                not isinstance(stage["depth_m"], int) or not 1 <= stage["depth_m"] <= 100 or
                not isinstance(stage["objects"], list)):
            raise ValueError("Размер или объекты сцены в файле шоу повреждены.")
        fixture_ids_for_stage = {fixture["id"] for fixture in data["fixtures"]}
        stage_object_ids = set()
        for item in stage["objects"]:
            if not isinstance(item, dict) or not isinstance(item.get("id"), str) or item["id"] in stage_object_ids:
                raise ValueError("В раскладке сцены найден объект без уникального ID.")
            stage_object_ids.add(item["id"])
            if item.get("kind") not in ("fixture", "musician", "label", "rect", "circle"):
                raise ValueError("В раскладке сцены указана неизвестная форма объекта.")
            if item.get("kind") == "fixture" and item.get("fixture_id") not in fixture_ids_for_stage:
                raise ValueError("В раскладке сцены есть ссылка на отсутствующий прибор.")
            for key in ("x", "y", "w", "h"):
                value = item.get(key, .5 if key in ("x", "y") else .12)
                if not isinstance(value, (int, float)) or not math.isfinite(value):
                    raise ValueError("Координаты объекта сцены повреждены.")
                item[key] = max(.02, min(.98, float(value)))
            item.setdefault("label", "Объект"); item.setdefault("color", "#61d9c3")
            color = item["color"]
            if not isinstance(color, str) or not color.startswith("#") or len(color) not in (4, 7) or not all(char in "0123456789abcdefABCDEF" for char in color[1:]):
                raise ValueError("В раскладке сцены указан неверный цвет.")
        scene_ids = set()
        for scene in data["scenes"]:
            if not isinstance(scene, dict) or not isinstance(scene.get("id"), str) or not isinstance(scene.get("look", {}), dict):
                raise ValueError("В файле найдена повреждённая сцена.")
            if scene["id"] in scene_ids:
                raise ValueError(f"ID сцены {scene['id']} повторяется.")
            scene_ids.add(scene["id"])
        for cue in data["cues"]:
            if not isinstance(cue, dict) or cue.get("scene_id") not in scene_ids:
                raise ValueError("В списке snapshots есть ссылка на отсутствующую сцену.")
            fade = cue.get("fade", 0)
            if not isinstance(fade, (int, float)) or not math.isfinite(fade) or not 0 <= fade <= 600:
                raise ValueError("Время перехода snapshot должно быть от 0 до 600 секунд.")
            cue.setdefault("update_method", "manual")
            if cue["update_method"] not in ("manual", "auto", "group", "relative", "absolute"):
                cue["update_method"] = "manual"
            cue.setdefault("update_channels", ["dimmer", "r", "g", "b", "w"])
            cue["update_channels"] = [key for key in cue["update_channels"] if key in ("dimmer", "r", "g", "b", "w")]
            cue.setdefault("update_fixtures", list(fixture_ids))
            cue["update_fixtures"] = [fixture_id for fixture_id in cue["update_fixtures"] if fixture_id in fixture_ids]
            cue.setdefault("update_group", [])
        for gang in data["gangs"]:
            if not isinstance(gang, dict) or not isinstance(gang.get("members"), list):
                raise ValueError("В файле найден некорректный GANG.")
            gang["members"] = [member for member in gang["members"] if member in fixture_ids]
            gang.setdefault("scope", ["dimmer", "r", "g", "b", "w"])
        mirror_groups = {}
        for fixture in data["fixtures"]:
            if fixture.get("mirror_group_id"):
                mirror_groups.setdefault(fixture["mirror_group_id"], []).append(fixture)
        for members in mirror_groups.values():
            shared_look = copy.deepcopy(members[0]["look"])
            for fixture in members:
                fixture["look"] = copy.deepcopy(shared_look)
            for scene in data["scenes"]:
                scene_look = scene.setdefault("look", {})
                shared_scene_look = copy.deepcopy(scene_look.get(members[0]["id"], shared_look))
                for fixture in members:
                    scene_look[fixture["id"]] = copy.deepcopy(shared_scene_look)

    def save_show(self):
        if not self.file_path:
            path = filedialog.asksaveasfilename(title="Сохранить шоу OLEG", defaultextension=".dmxshow",
                                                filetypes=[("Шоу OLEG", "*.dmxshow")],
                                                initialfile=f"{self.show['name'].replace(' ', '_')}.dmxshow")
            if not path:
                return
            target = Path(path)
        else:
            target = self.file_path
        try:
            self._validate_show_data(self.show)
            show_name = target.stem.replace("_", " ")
            data = copy.deepcopy(self.show)
            data["name"] = show_name
            target.parent.mkdir(parents=True, exist_ok=True)
            temp_path = None
            with tempfile.NamedTemporaryFile("w", encoding="utf-8", newline="\n", dir=target.parent,
                                             prefix=f".{target.name}.", suffix=".tmp", delete=False) as stream:
                temp_path = Path(stream.name)
                json.dump(data, stream, ensure_ascii=False, indent=2)
                stream.flush()
                os.fsync(stream.fileno())
            if target.exists():
                shutil.copy2(target, target.with_suffix(target.suffix + ".bak"))
            os.replace(temp_path, target)
            self.file_path = target
            self.show["name"] = show_name
            self.dirty = False
            self.show_title.configure(text=self.show["name"])
            self.status_var.set(f"СОХРАНЕНО ЛОКАЛЬНО · {target.name}")
        except Exception as exc:
            if 'temp_path' in locals() and temp_path and temp_path.exists():
                try:
                    temp_path.unlink()
                except OSError:
                    pass
            messagebox.showerror("Сохранить шоу", f"Не удалось сохранить шоу:\n{exc}")

    def _close(self):
        if self.dirty:
            choice = messagebox.askyesnocancel("Несохранённое шоу", "Сохранить изменения перед закрытием?")
            if choice is None:
                return
            if choice:
                self.save_show()
                if self.dirty:
                    return
        self._save_ui_preferences()
        self.output.disconnect()
        self.root.destroy()


def main():
    root = tk.Tk()
    LumaApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
