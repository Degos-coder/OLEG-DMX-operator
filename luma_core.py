"""Application domain helpers shared by the Qt UI and integrations.

Codex-authored changes are listed in CODEX_WORK_LOG.md as Written by Codex.
"""
from __future__ import annotations

import copy
import json
import math
import threading
import time
import uuid

APP_VERSION = "Alpha 0.4"
APP_NAME = "OLEG"
DEFAULT_GROUPS = ["Передний план", "Сцена", "Задник"]
SLOT_SIZE = 16

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

    def __init__(self, on_error=None):
        self.port = None
        self.thread = None
        self.stop_event = threading.Event()
        self.lock = threading.Lock()
        self.frame = bytes(513)
        self.error = None
        self.on_error = on_error
        self.generation = 0

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
        generation = self.generation
        self.thread = threading.Thread(target=self._run, args=(generation,), daemon=True)
        self.thread.start()

    def _run(self, generation):
        while not self.stop_event.is_set() and generation == self.generation:
            with self.lock:
                payload = self.frame
            # ENTTEC USB DMX PRO: 0x7e, Send DMX label 6, length, start code + slots, 0xe7.
            length = len(payload)
            packet = bytes((0x7E, 6, length & 0xFF, (length >> 8) & 0xFF)) + payload + bytes((0xE7,))
            try:
                if self.port and self.port.is_open:
                    self.port.write(packet)
            except Exception as exc:
                if generation != self.generation:
                    break
                self.error = str(exc)
                self.stop_event.set()
                if self.on_error:
                    try:
                        self.on_error(self.error, generation)
                    except Exception:
                        pass
                break
            self.stop_event.wait(0.04)

    def send_frame(self, channels: bytes):
        with self.lock:
            self.frame = bytes((0,)) + channels[:512].ljust(512, b"\0")

    def disconnect(self):
        self.generation += 1
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

class ShowSchema:
    @staticmethod
    def migrate(data):
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
        stage = data["stage"] if isinstance(data["stage"], dict) else {}
        layouts = stage.get("layouts", [])
        if not isinstance(layouts, list):
            layouts = []
        if not layouts:
            layout_id = uid()
            stage["layouts"] = [{"id": layout_id, "name": "Основная сцена",
                                 "objects": copy.deepcopy(stage.get("objects", []))}]
            stage["active_layout_id"] = layout_id
        elif not stage.get("active_layout_id"):
            stage["active_layout_id"] = layouts[0].get("id") if isinstance(layouts[0], dict) else None
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
            cue.setdefault("stage_layout_id", stage.get("active_layout_id"))
            cue.setdefault("update_method", "manual")
            cue.setdefault("update_channels", ["dimmer", "r", "g", "b", "w"])
            cue.setdefault("update_fixtures", [fixture.get("id") for fixture in data["fixtures"] if isinstance(fixture, dict)])
            cue.setdefault("update_group", [])
        if data.get("name") == "Untitled Show":
            data["name"] = "Новое шоу"

    @staticmethod
    def validate(data):
        if not isinstance(data, dict) or data.get("format") != "luma-dmx-show" or not isinstance(data.get("fixtures"), list):
            raise ValueError("Это не корректный файл шоу OLEG DMX.")
        if not isinstance(data.get("name"), str) or not data["name"].strip():
            raise ValueError("В файле шоу должно быть непустое название.")
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
        stage.setdefault("layouts", [])
        if (not isinstance(stage["width_m"], int) or not 1 <= stage["width_m"] <= 100 or
                not isinstance(stage["depth_m"], int) or not 1 <= stage["depth_m"] <= 100 or
                not isinstance(stage["objects"], list) or not isinstance(stage["layouts"], list)):
            raise ValueError("Размер или объекты сцены в файле шоу повреждены.")
        layout_ids = set()
        for layout in stage["layouts"]:
            if (not isinstance(layout, dict) or not isinstance(layout.get("id"), str) or
                    layout["id"] in layout_ids or not isinstance(layout.get("objects"), list)):
                raise ValueError("В сохранённых планах сцены найден повреждённый план.")
            layout_ids.add(layout["id"])
            layout.setdefault("name", "Сцена")
        if stage["layouts"] and stage.get("active_layout_id") not in layout_ids:
            raise ValueError("Текущий план сцены не найден среди сохранённых планов.")
        for cue in data["cues"]:
            layout_id = cue.get("stage_layout_id") if isinstance(cue, dict) else None
            if layout_id is not None and layout_id not in layout_ids:
                raise ValueError("Snapshot ссылается на отсутствующий план сцены.")
        fixture_ids_for_stage = {fixture["id"] for fixture in data["fixtures"]}
        object_lists = [stage["objects"], *(layout["objects"] for layout in stage["layouts"])]
        for object_list in object_lists:
            stage_object_ids = set()
            for item in object_list:
                if not isinstance(item, dict) or not isinstance(item.get("id"), str) or item["id"] in stage_object_ids:
                    raise ValueError("В раскладке сцены найден объект без уникального ID.")
                stage_object_ids.add(item["id"])
                if item.get("kind") not in ("fixture", "musician", "label", "rect", "circle", "column"):
                    raise ValueError("В раскладке сцены указана неизвестная форма объекта.")
                if item.get("kind") == "fixture" and item.get("fixture_id") not in fixture_ids_for_stage:
                    raise ValueError("В раскладке сцены есть ссылка на отсутствующий прибор.")
                for key in ("x", "y", "w", "h"):
                    value = item.get(key, .5 if key in ("x", "y") else .12)
                    if not isinstance(value, (int, float)) or not math.isfinite(value):
                        raise ValueError("Координаты объекта сцены повреждены.")
                    number = float(value)
                    item[key] = number if key in ("x", "y") else max(.02, min(.98, number))
                item.setdefault("label", "Объект"); item.setdefault("color", "#61d9c3")
                for key, default, low, high in (("rotation", 0, -180, 180), ("beam_length", 2.2, .45, 5), ("beam_size", .8, .25, 2)):
                    value = item.get(key, default)
                    if not isinstance(value, (int, float)) or not math.isfinite(value):
                        value = default
                    item[key] = max(low, min(high, float(value)))
                color = item["color"]
                if not isinstance(color, str) or not color.startswith("#") or len(color) not in (4, 7) or not all(char in "0123456789abcdefABCDEF" for char in color[1:]):
                    raise ValueError("В раскладке сцены указан неверный цвет.")
        scene_ids = set()
        for scene in data["scenes"]:
            if (not isinstance(scene, dict) or not isinstance(scene.get("id"), str) or
                    not isinstance(scene.get("look", {}), dict)):
                raise ValueError("В файле найдена повреждённая сцена.")
            if scene["id"] in scene_ids:
                raise ValueError(f"ID сцены {scene['id']} повторяется.")
            scene_ids.add(scene["id"])
        fixture_ids_for_looks = {fixture["id"] for fixture in data["fixtures"]}
        for scene in data["scenes"]:
            ShowSchema._validate_look_map(scene.get("look", {}), fixture_ids_for_looks, "сцены")
        cue_ids = set()
        for cue in data["cues"]:
            if not isinstance(cue, dict) or cue.get("scene_id") not in scene_ids:
                raise ValueError("В списке snapshots есть ссылка на отсутствующую сцену.")
            cue_id = cue.get("id")
            if not isinstance(cue_id, str) or not cue_id.strip():
                raise ValueError("У snapshot отсутствует корректный ID.")
            if cue_id in cue_ids:
                raise ValueError(f"ID snapshot {cue_id} повторяется.")
            cue_ids.add(cue_id)
            if not isinstance(cue.get("label"), str) or not cue["label"].strip():
                raise ValueError("У snapshot должно быть непустое название.")
            if not isinstance(cue.get("look"), dict):
                raise ValueError(f"В snapshot «{cue['label']}» повреждены уровни света.")
            ShowSchema._validate_look_map(cue["look"], fixture_ids_for_looks, f"snapshot «{cue['label']}»")
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

    @staticmethod
    def _validate_look_map(look_map, fixture_ids, context):
        if not isinstance(look_map, dict):
            raise ValueError(f"В {context} повреждён список уровней света.")
        for fixture_id, look in look_map.items():
            if fixture_id not in fixture_ids or not isinstance(look, dict):
                raise ValueError(f"В {context} найдены уровни света для неизвестного прибора.")
            for key, value in look.items():
                if key not in ("dimmer", "r", "g", "b", "w"):
                    raise ValueError(f"В {context} указан неизвестный канал света.")
                if (not isinstance(value, (int, float)) or not math.isfinite(value) or
                        not 0 <= value <= 255):
                    raise ValueError(f"В {context} значение канала должно быть от 0 до 255.")
