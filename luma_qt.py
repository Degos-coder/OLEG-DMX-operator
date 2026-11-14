"""OLEG's Qt desktop interface.

The show file stays a plain, versioned document.  The scene renderer, DMX
sender, and future network integrations are kept behind separate boundaries
so the UI can grow without binding those systems together.

Codex-authored changes are listed in CODEX_WORK_LOG.md as Written by Codex.
"""

from __future__ import annotations

import copy
import json
import math
import os
import re
import time
import uuid
from pathlib import Path

from PySide6.QtCore import QLineF, QMimeData, QPointF, QRectF, QSize, Qt, QTimer, Signal
from PySide6.QtGui import QColor, QConicalGradient, QDrag, QPainter, QPainterPath, QPen, QBrush, QFont, QFontDatabase, QPolygonF, QRadialGradient, QShortcut, QKeySequence
from PySide6.QtNetwork import QAbstractSocket, QTcpSocket
from PySide6.QtWidgets import (
    QApplication, QComboBox, QDialog, QDialogButtonBox, QDoubleSpinBox,
    QFileDialog, QFrame, QGraphicsObject, QGraphicsScene, QGraphicsSimpleTextItem, QGraphicsView, QInputDialog,
    QGridLayout, QHBoxLayout, QLabel, QLayout, QLineEdit, QListWidget, QListWidgetItem, QMainWindow,
    QMenu, QMessageBox, QPushButton, QSlider, QSpinBox, QStackedWidget, QTabWidget,
    QCheckBox, QScrollArea, QSplitter,
    QStyledItemDelegate, QStyleOptionViewItem, QTableWidget, QTableWidgetItem, QVBoxLayout, QWidget,
)

from luma_core import APP_NAME, APP_VERSION, DEFAULT_GROUPS, DmxOutput, ShowSchema, blank_look, default_show


BG = "#090c11"
SURFACE = "#121720"
SURFACE_2 = "#19212c"
SURFACE_3 = "#222d39"
LINE = "#2a3542"
TEXT = "#eef3f7"
MUTED = "#9aa8b7"
ACCENT = "#9bd8e8"
ACCENT_DARK = "#1b3540"
MINT = "#83dfc5"
RED = "#ff7586"
AMBER = "#f1c978"
STAGE_BG = "#0d151d"


def new_id() -> str:
    return uuid.uuid4().hex[:10]


def button(text: str, command=None, primary: bool = False, danger: bool = False) -> QPushButton:
    result = QPushButton(text)
    result.setCursor(Qt.CursorShape.PointingHandCursor)
    result.setProperty("role", "danger" if danger else "primary" if primary else "default")
    if command is not None:
        result.clicked.connect(command)
    return result


def label(text: str, style: str = "body") -> QLabel:
    result = QLabel(text)
    result.setProperty("role", style)
    return result


class ColorWheel(QWidget):
    colorSelected = Signal(object)
    colorStarted = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self._color = QColor("#ffffff")
        self.setMinimumSize(112, 112)
        self.setMaximumHeight(178)
        self.setToolTip("Выберите оттенок и насыщенность на цветовом круге")

    def sizeHint(self):
        window = self.window()
        scale = max(.75, min(1.45, float(getattr(window, "ui_scale", 1.0))))
        diameter = max(112, round(160 * scale))
        return QSize(diameter, diameter)

    def setColor(self, color):
        self._color = QColor(color)
        self.update()

    def _wheel_geometry(self):
        radius = max(10, min(self.width(), self.height()) / 2 - 8)
        return QPointF(self.width() / 2, self.height() / 2), radius

    def paintEvent(self, _event):
        center, radius = self._wheel_geometry()
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        wheel = QRectF(center.x() - radius, center.y() - radius, radius * 2, radius * 2)
        # QConicalGradient interpolates counter-clockwise. Start at the top
        # and reverse the stops so its painted hue follows the clockwise
        # screen-angle convention used by _choose_at().
        hue = QConicalGradient(center, 90)
        for stop, color in ((0, "#ff0000"), (1/6, "#ff00ff"), (2/6, "#0000ff"),
                            (3/6, "#00ffff"), (4/6, "#00ff00"), (5/6, "#ffff00"), (1, "#ff0000")):
            hue.setColorAt(stop, QColor(color))
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(hue)
        painter.drawEllipse(wheel)
        saturation = QRadialGradient(center, radius)
        saturation.setColorAt(0, QColor(255, 255, 255, 255))
        saturation.setColorAt(.98, QColor(255, 255, 255, 0))
        painter.setBrush(saturation)
        painter.drawEllipse(wheel)
        painter.setPen(QPen(QColor(LINE), 1.5))
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.drawEllipse(wheel)
        hue_value, sat_value, _value = self._color.getHsv()[:3]
        if hue_value < 0: hue_value = 0
        angle = math.radians(hue_value)
        marker = QPointF(center.x() + math.sin(angle) * radius * sat_value / 255,
                         center.y() - math.cos(angle) * radius * sat_value / 255)
        painter.setPen(QPen(QColor("#10151d"), 3))
        painter.setBrush(QColor("#ffffff"))
        painter.drawEllipse(marker, 6, 6)

    def _choose_at(self, point):
        center, radius = self._wheel_geometry()
        dx, dy = point.x() - center.x(), point.y() - center.y()
        distance = math.hypot(dx, dy)
        if distance > radius + 5:
            return
        hue = round((math.degrees(math.atan2(dx, -dy)) + 360) % 360)
        saturation = round(min(1, distance / radius) * 255)
        self._color = QColor.fromHsv(hue, saturation, 255)
        self.update()
        self.colorSelected.emit(QColor(self._color))

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.colorStarted.emit()
            self._choose_at(event.position())
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if event.buttons() & Qt.MouseButton.LeftButton:
            self._choose_at(event.position())
            event.accept()
            return
        super().mouseMoveEvent(event)


class StageObject(QGraphicsObject):
    """Scalable, movable object on the common live/snapshot stage plan."""

    def __init__(self, data: dict, changed, selected, color_override=None, readonly=False, label_scale=1.0):
        super().__init__()
        self.data = data
        self.changed = changed
        self.selected = selected
        self.color_override = color_override
        self.readonly = readonly
        self.w = max(.02, float(data.get("w", .12))) * 1000
        self.h = max(.02, float(data.get("h", .14))) * 620
        self._resize = None
        self._last = QPointF()
        self._rotation_start = 0.0
        self.setTransformOriginPoint(self.w / 2, self.h / 2)
        self.setRotation(float(data.get("rotation", 0)))
        flags = (QGraphicsObject.GraphicsItemFlag.ItemIsSelectable
                 | QGraphicsObject.GraphicsItemFlag.ItemSendsGeometryChanges)
        if not readonly:
            flags |= QGraphicsObject.GraphicsItemFlag.ItemIsMovable
        self.setFlags(flags)
        self.setAcceptHoverEvents(not readonly)
        # Keep fixtures and light cones visually above all stage references.
        self.setZValue(1000 if data.get("kind") == "fixture" else 4)
        self.setPos(float(data.get("x", .5)) * 1000, float(data.get("y", .5)) * 620)
        self.setToolTip(data.get("label", "Объект сцены"))
        self._stage_label = None
        if data.get("kind") in ("fixture", "musician"):
            self._stage_label = QGraphicsSimpleTextItem(str(data.get("label", "Объект")), self)
            self._stage_label.setBrush(QColor("#f1f5fa"))
            font = QFont("Segoe UI")
            font.setPixelSize(max(10, round(11 * label_scale)))
            font.setWeight(QFont.Weight.DemiBold)
            self._stage_label.setFont(font)
            self._stage_label.setFlag(QGraphicsObject.GraphicsItemFlag.ItemIgnoresTransformations, True)
            self._stage_label.setAcceptedMouseButtons(Qt.MouseButton.NoButton)
            self._stage_label.setZValue(2)
            self._position_stage_label()

    def boundingRect(self) -> QRectF:
        extra_bottom = self._beam_length() + self.h * .58 if self.data.get("kind") == "fixture" else 0
        margin = max(14, self.w * .9) if self.data.get("kind") == "fixture" else 14
        return QRectF(-margin, -28, self.w + margin * 2,
                      max(self.h + (14 if self._stage_label else 0), extra_bottom) + 28)

    def shape(self) -> QPainterPath:
        """Use the visible object and its controls for mouse hits, not the large paint bounds."""
        path = QPainterPath()
        rect = QRectF(1, 1, self.w - 2, self.h - 2)
        kind = self.data.get("kind", "label")
        if kind == "fixture":
            center = QPointF(self.w / 2, self.h * .34)
            path.addEllipse(center, max(6, self.w * .22), max(6, self.h * .22))
            if not self.readonly and self.isSelected():
                end = self._beam_end()
                spread = max(.25, min(2.0, float(self.data.get("beam_size", .8))))
                half = max(self.w * .10, self.w * .34 * spread)
                for point in (QPointF(end.x() - half, end.y()), end,
                              QPointF(end.x() + half, end.y())):
                    path.addEllipse(point, 9, 9)
        elif kind == "circle":
            path.addEllipse(rect)
        elif kind == "column":
            radius = min(18, rect.width() * .18)
            path.addRoundedRect(rect, radius, radius)
        elif kind in ("rect", "label", "musician"):
            path.addRoundedRect(rect, 12, 12)
        else:
            path.addRect(rect)
        if not self.readonly and self.isSelected():
            for point in (QPointF(0, 0), QPointF(self.w / 2, 0), QPointF(self.w, 0),
                          QPointF(self.w, self.h / 2), QPointF(self.w, self.h),
                          QPointF(self.w / 2, self.h), QPointF(0, self.h),
                          QPointF(0, self.h / 2), QPointF(self.w / 2, -18)):
                path.addRect(QRectF(point.x() - 8, point.y() - 8, 16, 16))
        return path

    def _beam_length(self):
        return max(.45, min(5.0, float(self.data.get("beam_length", 2.2)))) * self.h

    def _beam_end(self):
        return QPointF(self.w / 2, self.h * .48 + self._beam_length())

    def _handle_at(self, point):
        if self.readonly or not self.isSelected():
            return None
        if self.data.get("kind") == "fixture":
            end = self._beam_end()
            spread = max(.25, min(2.0, float(self.data.get("beam_size", .8))))
            half_width = max(self.w * .10, self.w * .34 * spread)
            if QLineF(point, QPointF(end.x() - half_width, end.y())).length() < 12:
                return "beam_width_left"
            if QLineF(point, QPointF(end.x() + half_width, end.y())).length() < 12:
                return "beam_width_right"
            if QLineF(point, end).length() < 13:
                return "beam"
        rotate = QPointF(self.w / 2, -18)
        if QLineF(point, rotate).length() < 12:
            return "rotate"
        handles = {
            "nw": QPointF(0, 0), "n": QPointF(self.w / 2, 0), "ne": QPointF(self.w, 0),
            "e": QPointF(self.w, self.h / 2), "se": QPointF(self.w, self.h),
            "s": QPointF(self.w / 2, self.h), "sw": QPointF(0, self.h), "w": QPointF(0, self.h / 2),
        }
        return next((name for name, center in handles.items()
                     if QRectF(center.x() - 8, center.y() - 8, 16, 16).contains(point)), None)

    def _position_stage_label(self):
        if self._stage_label is None:
            return
        bounds = self._stage_label.boundingRect()
        self._stage_label.setPos((self.w - bounds.width()) / 2, self.h + 1)

    def paint(self, painter: QPainter, _option, _widget=None):
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        rect = QRectF(1, 1, self.w - 2, self.h - 2)
        kind = self.data.get("kind", "label")
        tint = QColor(self.color_override or self.data.get("color", ACCENT))
        tint.setAlpha(38)
        edge = QColor(self.color_override or self.data.get("color", ACCENT))
        edge.setAlpha(190)
        painter.setPen(QPen(edge if self.isSelected() else QColor(edge.red(), edge.green(), edge.blue(), 95), 2 if self.isSelected() else 1))
        painter.setBrush(QBrush(tint if kind in ("musician", "label") else QColor(255, 255, 255, 18)))
        if kind == "circle":
            painter.drawEllipse(rect)
        elif kind == "rect":
            painter.drawRoundedRect(rect, 12, 12)
        elif kind == "column":
            radius = min(18, rect.width() * .18)
            painter.drawRoundedRect(rect, radius, radius)
            painter.setPen(QPen(QColor(edge.red(), edge.green(), edge.blue(), 90), 1))
            for fraction in (.33, .66):
                x = rect.left() + rect.width() * fraction
                painter.drawLine(QPointF(x, rect.top() + 5), QPointF(x, rect.bottom() - 5))
        elif kind == "fixture":
            beam_color = QColor(self.color_override or "#26303a")
            lit = beam_color.name() != "#26303a"
            cx = rect.center().x()
            spread = max(.25, min(2.0, float(self.data.get("beam_size", .8))))
            end = self._beam_end()
            base_y = rect.top() + rect.height() * .48
            end_width = max(rect.width() * .10, rect.width() * .34 * spread)
            distance = max(0.0, end.y() - base_y)
            # Layered translucent cones create a soft edge; the feather grows with throw distance.
            feather = min(rect.width() * .45, distance * .12)
            painter.setPen(Qt.PenStyle.NoPen)
            for expansion, alpha in ((1.0, 8), (.82, 12), (.60, 18), (.38, 22)):
                color = QColor(beam_color); color.setAlpha(alpha if lit else 2)
                half = end_width * expansion + feather * (1.0 - expansion)
                painter.setBrush(color)
                painter.drawPolygon(QPolygonF([QPointF(cx - rect.width() * .10, base_y),
                                               QPointF(cx + rect.width() * .10, base_y),
                                               QPointF(cx + half, end.y()), QPointF(cx - half, end.y())]))
            endpoint_radius = min(rect.width() * .38, rect.width() * .08 + distance * .075)
            halo = QRadialGradient(end, endpoint_radius)
            halo.setColorAt(0, QColor(beam_color.red(), beam_color.green(), beam_color.blue(), 52 if lit else 3))
            halo.setColorAt(.65, QColor(beam_color.red(), beam_color.green(), beam_color.blue(), 15 if lit else 1))
            halo.setColorAt(1, QColor(beam_color.red(), beam_color.green(), beam_color.blue(), 0))
            painter.setBrush(halo)
            painter.drawEllipse(end, endpoint_radius, endpoint_radius)
            center = QPointF(cx, rect.top() + rect.height() * .34)
            radius = min(rect.width(), rect.height()) * .27
            halo = QRadialGradient(center, radius)
            halo.setColorAt(0, QColor(beam_color.red(), beam_color.green(), beam_color.blue(), 220 if lit else 75))
            halo.setColorAt(.55, QColor(beam_color.red(), beam_color.green(), beam_color.blue(), 100 if lit else 22))
            halo.setColorAt(1, QColor(beam_color.red(), beam_color.green(), beam_color.blue(), 0))
            painter.setBrush(halo)
            painter.drawEllipse(center, radius, radius)
            painter.setBrush(QColor(beam_color.red(), beam_color.green(), beam_color.blue(), 235 if lit else 100))
            painter.setPen(QPen(QColor(beam_color.red(), beam_color.green(), beam_color.blue(), 245 if lit else 120), 2))
            painter.drawEllipse(center, max(6, rect.width() * .22), max(6, rect.height() * .22))
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QColor("#fff5dd") if lit else QColor("#788491"))
            painter.drawEllipse(center, max(3, rect.width() * .055), max(3, rect.height() * .055))
        elif kind == "musician":
            painter.drawRoundedRect(rect, 16, 16)
            self._paint_musician(painter, rect)
        elif kind == "label":
            painter.drawRoundedRect(rect, 12, 12)
        else:
            painter.drawRect(rect)
        if kind not in ("fixture", "musician"):
            painter.setPen(QColor(244, 244, 250))
            font = painter.font()
            font.setFamily("Segoe UI")
            font.setWeight(QFont.Weight.DemiBold)
            font.setPointSizeF(max(9, min(16, rect.height() * .16)))
            painter.setFont(font)
            painter.drawText(rect.adjusted(7, 3, -7, -3), Qt.AlignmentFlag.AlignCenter | Qt.TextFlag.TextWordWrap,
                             str(self.data.get("label", "Ориентир")))
        if self.isSelected() and not self.readonly:
            painter.setPen(QPen(QColor("#15222a"), 1))
            painter.setBrush(QColor(ACCENT))
            handles = [QPointF(0, 0), QPointF(self.w / 2, 0), QPointF(self.w, 0),
                       QPointF(self.w, self.h / 2), QPointF(self.w, self.h),
                       QPointF(self.w / 2, self.h), QPointF(0, self.h), QPointF(0, self.h / 2)]
            for point in handles:
                painter.drawRect(QRectF(point.x() - 4, point.y() - 4, 8, 8))
            painter.setPen(QPen(QColor(ACCENT), 1.5))
            painter.drawLine(QPointF(self.w / 2, 0), QPointF(self.w / 2, -18))
            painter.setBrush(QColor("#f5fbff"))
            painter.drawEllipse(QPointF(self.w / 2, -18), 5, 5)
            if kind == "fixture":
                painter.setPen(QPen(QColor("#15222a"), 1))
                painter.setBrush(QColor("#ffd166"))
                end = self._beam_end()
                spread = max(.25, min(2.0, float(self.data.get("beam_size", .8))))
                half_width = max(self.w * .10, self.w * .34 * spread)
                painter.drawEllipse(QPointF(end.x() - half_width, end.y()), 5, 5)
                painter.drawEllipse(QPointF(end.x() + half_width, end.y()), 5, 5)

    def _paint_musician(self, painter: QPainter, rect: QRectF):
        """Simple embedded stage pictogram; no external icon files required."""
        cx, cy = rect.center().x() - rect.width() * .10, rect.center().y() - 4
        size = min(rect.width(), rect.height())
        ink = QColor(247, 244, 255)
        painter.setPen(QPen(ink, max(3, size * .025), Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
        painter.setBrush(ink)
        painter.drawEllipse(QPointF(cx, cy - size * .2), size * .075, size * .075)
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.drawLine(QPointF(cx, cy - size * .11), QPointF(cx, cy + size * .12))
        painter.drawLine(QPointF(cx, cy - size * .02), QPointF(cx - size * .13, cy + size * .04))
        painter.drawLine(QPointF(cx, cy - size * .02), QPointF(cx + size * .12, cy - size * .08))
        painter.drawLine(QPointF(cx, cy + size * .12), QPointF(cx - size * .11, cy + size * .26))
        painter.drawLine(QPointF(cx, cy + size * .12), QPointF(cx + size * .1, cy + size * .26))
        instrument = self.data.get("instrument", "guitar")
        painter.setPen(QPen(QColor(255, 255, 255, 205), max(2, size * .018), Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap))
        painter.setBrush(QColor(247, 244, 255, 65))
        if instrument in ("guitar", "bass"):
            is_bass = instrument == "bass"
            body = QRectF(cx + size * .045, cy - size * .065,
                          size * (.145 if is_bass else .12), size * .12)
            neck_end = QPointF(cx + size * (.31 if is_bass else .27), cy - size * .27)
            painter.drawEllipse(body)
            painter.drawLine(QPointF(body.center().x(), body.center().y()), neck_end)
            painter.drawLine(neck_end, QPointF(neck_end.x() + size * .045, neck_end.y() - size * .018))
            if is_bass:
                # Four parallel strings and two pickups distinguish a bass at stage scale.
                painter.setPen(QPen(QColor(247, 244, 255, 175), max(1, size * .007)))
                for offset in (-.018, -.006, .006, .018):
                    painter.drawLine(QPointF(body.center().x() + size * offset, body.center().y() - size * .025),
                                     QPointF(neck_end.x() - size * .02, neck_end.y() + size * .03))
                painter.setPen(QPen(QColor(247, 244, 255, 185), max(2, size * .012)))
                painter.drawRoundedRect(QRectF(body.center().x() - size * .035, body.center().y() - size * .018,
                                               size * .07, size * .025), 2, 2)
                painter.drawRoundedRect(QRectF(body.center().x() - size * .03, body.center().y() + size * .025,
                                               size * .06, size * .022), 2, 2)
            else:
                painter.setPen(QPen(QColor(247, 244, 255, 185), max(1, size * .008)))
                painter.drawEllipse(body.center(), size * .018, size * .018)
        elif instrument == "vocal":
            mic = QPointF(cx + size * .21, cy - size * .22)
            painter.drawEllipse(mic, size * .025, size * .035)
            painter.drawLine(mic, QPointF(cx + size * .19, cy + size * .12))
            painter.drawLine(QPointF(cx + size * .14, cy + size * .12), QPointF(cx + size * .24, cy + size * .12))
        elif instrument == "keys":
            keyboard = QRectF(cx + size * .08, cy + size * .10, size * .29, size * .085)
            painter.drawRoundedRect(keyboard, 3, 3)
            painter.setPen(QPen(QColor(20, 20, 28, 220), max(1, size * .008)))
            for index in range(1, 8):
                x = keyboard.left() + keyboard.width() * index / 8
                painter.drawLine(QPointF(x, keyboard.top()), QPointF(x, keyboard.bottom()))
        elif instrument == "drums":
            for dx, dy, radius in ((.12, .05, .07), (.27, .02, .055), (.19, .16, .06)):
                center = QPointF(cx + size * dx, cy + size * dy)
                painter.drawEllipse(center, size * radius, size * radius * .62)
                painter.drawLine(QPointF(center.x(), center.y() + size * radius * .5), QPointF(center.x(), cy + size * .29))
    def mousePressEvent(self, event):
        view = self.scene().views()[0] if self.scene() and self.scene().views() else None
        preserve_multi = self.isSelected() and self.scene() and len(self.scene().selectedItems()) > 1
        if view:
            view._preserve_multi_selection = bool(preserve_multi)
        self.selected(self.data.get("id"))
        if view:
            view._preserve_multi_selection = False
        if self.scene() and self.scene().views(): self.scene().views()[0].setFocus()
        self._last = event.pos()
        self._resize = self._handle_at(event.pos())
        self._transform_started = False
        if self._resize:
            if self._resize == "rotate":
                center = QPointF(self.w / 2, self.h / 2)
                self._rotation_start = math.degrees(math.atan2(event.pos().y() - center.y(), event.pos().x() - center.x()))
                self._rotation_value = float(self.data.get("rotation", 0))
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self.readonly:
            event.ignore()
            return
        if self._resize:
            if not self._transform_started:
                self.changed({"begin_transform": True})
                self._transform_started = True
            p = event.pos()
            self.prepareGeometryChange()
            dx, dy = p.x() - self._last.x(), p.y() - self._last.y()
            if self._resize == "beam":
                self.data["beam_length"] = max(.45, min(5.0, (p.y() - self.h * .48) / max(1, self.h)))
            elif self._resize in ("beam_width_left", "beam_width_right"):
                half = abs(p.x() - self.w / 2)
                self.data["beam_size"] = max(.25, min(2.0, half / max(1, self.w * .34)))
            elif self._resize == "rotate":
                center = QPointF(self.w / 2, self.h / 2)
                angle = math.degrees(math.atan2(p.y() - center.y(), p.x() - center.x()))
                rotation = (self._rotation_value + angle - self._rotation_start + 360) % 360
                if rotation > 180: rotation -= 360
                self.data["rotation"] = rotation
                self.setRotation(rotation)
            else:
                handle = self._resize
                if handle in ("e", "ne", "se"): self.w = max(20, min(980, self.w + dx))
                if handle in ("w", "nw", "sw"): self.w = max(20, min(980, self.w - dx)); self.setX(self.x() + dx)
                if handle in ("s", "se", "sw"): self.h = max(20, min(620, self.h + dy))
                if handle in ("n", "nw", "ne"): self.h = max(20, min(620, self.h - dy)); self.setY(self.y() + dy)
                self.setTransformOriginPoint(self.w / 2, self.h / 2)
                self.data["w"], self.data["h"] = self.w / 1000, self.h / 620
                self._position_stage_label()
                self._last = p
            self.update()
            event.accept()
            return
        if not self._transform_started:
            self.changed({"begin_transform": True})
            self._transform_started = True
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self.readonly:
            super().mouseReleaseEvent(event)
            return
        if self._transform_started and self.scene():
            moved_items = [item for item in self.scene().selectedItems()
                           if isinstance(item, StageObject) and not item.readonly]
            if not moved_items:
                moved_items = [self]
            for item in moved_items:
                item.data["x"] = item.pos().x() / 1000
                item.data["y"] = item.pos().y() / 620
                item.setPos(item.data["x"] * 1000, item.data["y"] * 620)
        self._resize = False
        super().mouseReleaseEvent(event)
        if self._transform_started:
            changed = self.changed
            object_id = self.data.get("id")
            QTimer.singleShot(0, lambda: changed({"geometry_commit": True, "object_id": object_id}))
        self._transform_started = False

    def hoverMoveEvent(self, event):
        handle = self._handle_at(event.pos())
        cursors = {"n": Qt.CursorShape.SizeVerCursor, "s": Qt.CursorShape.SizeVerCursor,
                   "e": Qt.CursorShape.SizeHorCursor, "w": Qt.CursorShape.SizeHorCursor,
                   "ne": Qt.CursorShape.SizeBDiagCursor, "sw": Qt.CursorShape.SizeBDiagCursor,
                   "nw": Qt.CursorShape.SizeFDiagCursor, "se": Qt.CursorShape.SizeFDiagCursor,
                   "rotate": Qt.CursorShape.CrossCursor, "beam": Qt.CursorShape.SizeVerCursor,
                   "beam_width_left": Qt.CursorShape.SizeHorCursor,
                   "beam_width_right": Qt.CursorShape.SizeHorCursor}
        self.setCursor(cursors.get(handle, Qt.CursorShape.OpenHandCursor))
        super().hoverMoveEvent(event)

    def contextMenuEvent(self, event):
        if self.readonly:
            event.ignore()
            return
        menu = QMenu()
        edit = menu.addAction("Настроить")
        copy_action = menu.addAction("Копировать")
        cut_action = menu.addAction("Вырезать")
        paste_action = menu.addAction("Вставить")
        view = self.scene().views()[0] if self.scene() and self.scene().views() else None
        clipboard = getattr(view.window(), "_clipboard", None) if view else None
        paste_action.setEnabled(bool(clipboard and clipboard[0] == "stage"))
        duplicate = menu.addAction("Создать копию")
        remove = menu.addAction("Удалить")
        selected = menu.exec(event.screenPos())
        if selected == edit:
            self.selected(self.data.get("id"))
            self.changed("edit")
        elif selected == copy_action:
            self.changed({"copy": self.data})
        elif selected == cut_action:
            self.changed({"cut": self.data})
        elif selected == paste_action:
            self.changed({"paste": True})
        elif selected == duplicate:
            self.changed({"duplicate": self.data})
        elif selected == remove:
            self.changed({"delete": self.data.get("id")})


class StageView(QGraphicsView):
    objectChanged = Signal(object)
    objectSelected = Signal(str)
    zoomChanged = Signal(float)
    selectionChanged = Signal()

    def __init__(self, parent=None, zoom_enabled=False):
        super().__init__(parent)
        self.zoom_enabled = zoom_enabled
        self.zoom_factor = 1.0
        self._preserve_multi_selection = False
        self.stage = QGraphicsScene(self)
        self.stage.selectionChanged.connect(self.selectionChanged.emit)
        self.setScene(self.stage)
        self.setSceneRect(0, 0, 1000, 700)
        self.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.SmoothPixmapTransform)
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setBackgroundBrush(QColor(STAGE_BG))
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.setDragMode(QGraphicsView.DragMode.RubberBandDrag)
        self.setAcceptDrops(True)
        self._show = None
        self._look = None
        self._selected_id = None
        self._readonly = False
        self._fit_timer = QTimer(self)
        self._fit_timer.setSingleShot(True)
        self._fit_timer.timeout.connect(self.fit_stage)

    def set_data(self, show: dict, look: dict | None = None, selected_id: str | None = None, readonly=False):
        self._show, self._look, self._selected_id, self._readonly = show, look, selected_id, readonly
        self.stage.clear()
        self.stage.setSceneRect(0, 0, 1000, 700)
        self._paint_room()
        fixtures = {fixture["id"]: fixture for fixture in show.get("fixtures", [])}
        for obj in self._objects_for_stage():
            fixture = fixtures.get(obj.get("fixture_id")) if obj.get("kind") == "fixture" else None
            color = self._fixture_color(fixture) if fixture else None
            item = StageObject(
                obj, self.objectChanged.emit, self._select_object,
                color_override=color, readonly=readonly,
                label_scale=getattr(self.window(), "ui_scale", 1.0),
            )
            item.setSelected(obj.get("id") == selected_id)
            self.stage.addItem(item)
        self._fit_timer.start(0)

    def _objects_for_stage(self):
        data = self._show.get("stage", {}).get("objects", [])
        if data:
            return data
        # A brand-new show has a useful preview without mutating the saved plan.
        fixtures = self._show.get("fixtures", [])
        count = max(1, len(fixtures))
        return [{"id": f"preview-{f['id']}", "kind": "fixture", "fixture_id": f["id"],
                 "label": f.get("name", "PAR"), "x": .14 + .72 * i / max(1, count - 1), "y": .16,
                 "w": .07, "h": .11, "color": self._fixture_color(f)}
                for i, f in enumerate(fixtures)]

    def _fixture_color(self, fixture):
        look = (self._look or {}).get(fixture["id"], {}) if self._look is not None else fixture.get("look", {})
        rgb = [max(0, min(255, int(look.get(key, 0)))) for key in ("r", "g", "b")]
        white = max(0, min(255, int(look.get("w", 0))))
        rgb = [min(255, value + round(white * .72)) for value in rgb]
        if max(rgb) == 0:
            return "#26303a"
        factor = max(0, min(255, float(look.get("dimmer", 255)))) / 255
        if factor == 0:
            return "#26303a"
        return QColor(round(rgb[0] * factor), round(rgb[1] * factor), round(rgb[2] * factor)).name()

    def _paint_room(self):
        border = QGraphicsObject
        del border
        stage_box = self.stage.addRect(QRectF(50, 45, 900, 590), QPen(QColor("#5c6572"), 1.4), QBrush(QColor("#17202a")))
        stage_box.setZValue(-2)
        # Fine drafting grid makes placement easier without competing with fixtures.
        grid = QPen(QColor(255, 255, 255, 11), 1)
        for x in range(100, 951, 50):
            self.stage.addLine(x, 45, x, 635, grid).setZValue(-1)
        for y in range(95, 636, 50):
            self.stage.addLine(50, y, 950, y, grid).setZValue(-1)

    def set_selected(self, object_id):
        self._selected_id = object_id
        if self._preserve_multi_selection and len(self.stage.selectedItems()) > 1:
            return
        for item in self.stage.items():
            if isinstance(item, StageObject):
                item.setSelected(item.data.get("id") == object_id)

    def _select_object(self, object_id):
        self.set_selected(object_id)
        self.objectSelected.emit(str(object_id))

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._fit_timer.start(0)

    def fit_stage(self):
        self.resetTransform()
        self.fitInView(self.sceneRect().adjusted(5, 5, -5, -5), Qt.AspectRatioMode.KeepAspectRatio)
        if self.zoom_enabled:
            self.scale(self.zoom_factor, self.zoom_factor)

    def set_zoom_factor(self, factor):
        self.zoom_factor = max(.55, min(2.4, float(factor)))
        policy = Qt.ScrollBarPolicy.ScrollBarAsNeeded if self.zoom_factor > 1.02 else Qt.ScrollBarPolicy.ScrollBarAlwaysOff
        self.setHorizontalScrollBarPolicy(policy)
        self.setVerticalScrollBarPolicy(policy)
        self.fit_stage()
        self.zoomChanged.emit(self.zoom_factor)

    def zoom_in(self):
        self.set_zoom_factor(self.zoom_factor * 1.2)

    def zoom_out(self):
        self.set_zoom_factor(self.zoom_factor / 1.2)

    def reset_zoom(self):
        self.set_zoom_factor(1.0)

    def wheelEvent(self, event):
        if self.zoom_enabled and event.angleDelta().y():
            self.set_zoom_factor(self.zoom_factor * (1.12 if event.angleDelta().y() > 0 else 1 / 1.12))
            event.accept()
            return
        super().wheelEvent(event)

    def dragEnterEvent(self, event):
        if event.mimeData().hasText() and not self._readonly:
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragMoveEvent(self, event):
        event.acceptProposedAction() if event.mimeData().hasText() and not self._readonly else event.ignore()

    def dropEvent(self, event):
        raw_kind = event.mimeData().text()
        kind, separator, instrument = raw_kind.partition(":")
        if kind in ("musician", "label", "rect", "circle"):
            pos = self.mapToScene(event.position().toPoint())
            payload = {"add": kind, "x": max(.05, min(.9, pos.x() / 1000)), "y": max(.05, min(.87, pos.y() / 620))}
            if separator: payload["instrument"] = instrument
            self.objectChanged.emit(payload)
            event.acceptProposedAction()


class CueTileDelegate(QStyledItemDelegate):
    """Compact cue cards for the live strip, with preview/live states made visible."""

    def __init__(self, window, parent=None):
        super().__init__(parent)
        self.window = window

    def sizeHint(self, option, index):
        return QSize(120, 56)

    def paint(self, painter, option: QStyleOptionViewItem, index):
        cue_id = index.data(Qt.ItemDataRole.UserRole)
        cue = next((entry for entry in self.window.show_data.get("cues", [])
                    if entry.get("id") == cue_id), None)
        if cue is None:
            return
        live = cue_id == self.window.live_cue_id
        preview = cue_id == self.window.preview_cue_id
        rect = option.rect.adjusted(2, 3, -2, -3)
        fill = QColor("#17312f") if live else QColor(ACCENT_DARK if preview else SURFACE_2)
        edge = QColor(MINT if live else ACCENT if preview else LINE)
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(QPen(edge, 1.4 if live or preview else 1))
        painter.setBrush(fill)
        painter.drawRoundedRect(rect, 9, 9)

        number_font = QFont(option.font)
        number_font.setPointSize(8)
        number_font.setWeight(QFont.Weight.Bold)
        painter.setFont(number_font)
        painter.setPen(QColor(MINT if live else ACCENT))
        number_rect = rect.adjusted(9, 5, -9, -rect.height() + 30)
        painter.drawText(number_rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                         f"{index.row() + 1:02d}")

        name_font = QFont(option.font)
        name_font.setPointSize(9)
        name_font.setWeight(QFont.Weight.DemiBold)
        painter.setFont(name_font)
        name = str(cue.get("label", "Snapshot"))
        name = option.fontMetrics.elidedText(name, Qt.TextElideMode.ElideRight, max(20, rect.width() - 42))
        title_rect = rect.adjusted(31, 5, -8, -rect.height() + 30)
        painter.setPen(QColor(TEXT))
        painter.drawText(title_rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, name)

        detail_font = QFont(option.font)
        detail_font.setPointSize(7)
        painter.setFont(detail_font)
        state = "В ЭФИРЕ" if live else "ПРЕДПРОСМОТР" if preview else "ПЕРЕХОД"
        detail_rect = rect.adjusted(10, 29, -8, -4)
        painter.setPen(QColor(MINT if live else MUTED))
        scene_number = self.window._scene_number_for_cue(cue)
        painter.drawText(detail_rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                         f"СЦЕНА {scene_number:02d} · {state} · {float(cue.get('fade', 0)):g} с")
        painter.restore()


class PaletteButton(QPushButton):
    def __init__(self, title: str, kind: str, parent=None):
        super().__init__(title, parent)
        self.kind = kind
        self._start = None
        self._dragged = False
        self.setCursor(Qt.CursorShape.OpenHandCursor)
        self.setToolTip("Нажмите, чтобы добавить в центр сцены, или перетащите в нужное место.")
    def mousePressEvent(self, event):
        self._start = event.position().toPoint()
        self._dragged = False
        super().mousePressEvent(event)
    def mouseMoveEvent(self, event):
        if self._start is not None and (event.position().toPoint() - self._start).manhattanLength() > QApplication.startDragDistance():
            self._dragged = True
            drag = QDrag(self)
            mime = QMimeData()
            mime.setText(self.kind)
            drag.setMimeData(mime)
            drag.exec(Qt.DropAction.CopyAction)
            return
        super().mouseMoveEvent(event)
    def mouseReleaseEvent(self, event):
        if self._dragged:
            self.setDown(False)
            self._dragged = False
            event.accept()
            return
        super().mouseReleaseEvent(event)


class OlegWindow(QMainWindow):
    dmx_write_failed = Signal(str, int)

    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"{APP_NAME} · {APP_VERSION}")
        self.resize(1500, 920)
        self.setMinimumSize(1180, 700)
        self.setObjectName("window")
        self.show_data = default_show()
        self.show_path: Path | None = None
        self.dirty = False
        self.blackout_active = False
        self.dmx_write_failed.connect(self._handle_dmx_write_failure)
        self.output = DmxOutput(on_error=self.dmx_write_failed.emit)
        self._fade = None
        self.fade_timer = QTimer(self)
        self.fade_timer.setInterval(33)
        self.fade_timer.timeout.connect(self._tick_fade)
        self.live_cue_id = None
        self.preview_cue_id = None
        self.selected_fixture_ids = {self.show_data["fixtures"][0]["id"]}
        self.gang_isolated_ids: set[str] = set()
        self.gang_fader_previous = {}
        self._preferences_path = self._get_preferences_path()
        self.saved_colors = self._load_saved_colors()
        self.ui_scale = self._load_ui_scale()
        self._saved_splitter_sizes = self._load_splitter_sizes()
        self._ui_scale_widgets = []
        self._ui_scale_layouts = []
        self._blackout_pulse = False
        self.blackout_timer = QTimer(self)
        self.blackout_timer.setInterval(420)
        self.blackout_timer.timeout.connect(self._pulse_blackout_edge)
        self.layout_preferences_timer = QTimer(self)
        self.layout_preferences_timer.setSingleShot(True)
        self.layout_preferences_timer.setInterval(350)
        self.layout_preferences_timer.timeout.connect(self._save_preferences)
        self.selected_stage_id = None
        self.undo_stack: list[dict] = []
        self.redo_stack: list[dict] = []
        self._clipboard = None
        self._build()
        self._capture_ui_metrics()
        self._apply_ui_scale(self.ui_scale, persist=False)
        self._setup_ui_scale_shortcuts()
        self._refresh_ports()
        self.refresh_all()
        QTimer.singleShot(0, self._restore_splitter_sizes)

    def _build(self):
        root = QWidget()
        root.setObjectName("root")
        self.setCentralWidget(root)
        outer = QVBoxLayout(root)
        outer.setContentsMargins(14, 14, 14, 12)
        outer.setSpacing(12)
        self.header = self._build_header()
        outer.addWidget(self.header)
        self.workspace_splitter = QSplitter(Qt.Orientation.Horizontal)
        self.workspace_splitter.setObjectName("workspaceSplitter")
        self.workspace_splitter.setHandleWidth(8)
        self.workspace_splitter.setChildrenCollapsible(False)
        outer.addWidget(self.workspace_splitter, 1)
        self.page_names = ["Консоль", "Сцена", "Snapshots", "Патч", "Связь"]
        self.sidebar = self._build_sidebar()
        self.workspace_splitter.addWidget(self.sidebar)
        self.pages = QStackedWidget()
        self.workspace_splitter.addWidget(self.pages)
        self.workspace_splitter.setStretchFactor(0, 0)
        self.workspace_splitter.setStretchFactor(1, 1)
        self.live_page = self._build_live_page()
        self.stage_page = self._build_stage_page()
        self.cues_page = self._build_cues_page()
        self.patch_page = self._build_patch_page()
        self.bridge_page = self._build_bridge_page()
        for page in (self.live_page, self.stage_page, self.cues_page, self.patch_page, self.bridge_page):
            self.pages.addWidget(page)
        self._select_page(0)
        self.status_bar = label("ОФЛАЙН · ШОУ СОХРАНЯЕТСЯ ЛОКАЛЬНО", "status")
        self.status_bar.setObjectName("statusBar")
        outer.addWidget(self.status_bar)
        self.setStyleSheet(self._stylesheet())
        self._connect_splitter(self.workspace_splitter)
        self.workspace_splitter.setSizes([210, 1290])

    def _build_header(self):
        panel = QFrame()
        panel.setObjectName("topbar")
        row = QGridLayout(panel)
        row.setContentsMargins(18, 12, 18, 12)
        row.setHorizontalSpacing(8)
        row.setVerticalSpacing(4)
        brand = label("OLEG", "brand")
        tagline = label("DMX  /  ЖИВОЙ СВЕТ", "eyebrow")
        self.show_name = label(self.show_data["name"], "showName")
        self.connection_badge = label("●  DMX ОТКЛЮЧЁН", "badge")
        self.open_button = button("Открыть", self._open_dialog)
        self.save_button = button("Сохранить", primary=True)
        self.save_button.clicked.connect(self._save_dialog)
        self.blackout_button = button("BLACKOUT", self._toggle_blackout, danger=True)
        self.blackout_button.setCheckable(True)
        self.blackout_button.setObjectName("blackoutButton")
        self.blackout_button.setProperty("pulse", "false")
        self.ui_scale_label = label("МАСШТАБ", "eyebrow")
        self.ui_scale_picker = QComboBox()
        self.ui_scale_picker.setToolTip("Размер интерфейса во всех вкладках · Ctrl +/− · Ctrl+0 — сброс")
        for percentage in (75, 85, 100, 115, 130, 145):
            self.ui_scale_picker.addItem(f"{percentage}%", percentage / 100)
        self.ui_scale_picker.currentIndexChanged.connect(self._ui_scale_picked)
        self.new_button = button("Создать")
        self.new_button.setToolTip("Создать новое шоу")
        self.new_button.clicked.connect(self._new_show)
        self._header_layout = row
        self._header_brand = brand
        self._header_tagline = tagline
        self._header_primary = (brand, tagline, self.show_name, self.connection_badge, self.blackout_button)
        self._header_secondary = (self.open_button, self.save_button, self.ui_scale_label,
                                  self.ui_scale_picker, self.new_button)
        self._header_is_compact = None
        self._update_header_layout()
        return panel

    def _update_header_layout(self):
        if not hasattr(self, "_header_layout"):
            return
        compact = self.width() < round(1320 * getattr(self, "ui_scale", 1.0))
        if compact == self._header_is_compact:
            return
        widgets = self._header_primary + self._header_secondary
        for widget in widgets:
            self._header_layout.removeWidget(widget)
        if compact:
            for column, widget in enumerate(self._header_primary):
                self._header_layout.addWidget(widget, 0, column)
            for column, widget in enumerate(self._header_secondary):
                self._header_layout.addWidget(widget, 1, column)
            self._header_layout.setColumnStretch(2, 1)
        else:
            for column, widget in enumerate(widgets):
                self._header_layout.addWidget(widget, 0, column)
            self._header_layout.setColumnStretch(2, 1)
        self._header_is_compact = compact

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._update_header_layout()

    def _build_sidebar(self):
        panel = QFrame()
        panel.setObjectName("sidebar")
        panel.setMinimumWidth(155)
        panel.setMaximumWidth(380)
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(10, 16, 10, 12)
        layout.setSpacing(6)
        layout.addWidget(label("РАБОЧЕЕ ПРОСТРАНСТВО", "eyebrow"))
        self.nav_buttons = []
        for index, name in enumerate(self.page_names):
            item = button(name)
            item.setCheckable(True)
            item.clicked.connect(lambda checked=False, i=index: self._select_page(i))
            self.nav_buttons.append(item)
            layout.addWidget(item)
        layout.addStretch(1)
        card = QFrame()
        card.setObjectName("miniCard")
        card_layout = QVBoxLayout(card)
        card_layout.addWidget(label("ПОДСКАЗКА", "eyebrow"))
        card_layout.addWidget(label(
            "F2  Редактор сцены или snapshot\nCtrl C/V  Коп./вставить\nCtrl X  Вырезать\n"
            "Ctrl Z  Отменить\nCtrl Shift Z  Повторить\nDelete  Удалить", "muted"))
        layout.addWidget(card)
        self._select_page(0)
        return panel

    def _panel(self, title: str, subtitle: str | None = None):
        frame = QFrame()
        frame.setObjectName("panel")
        layout = QVBoxLayout(frame)
        layout.setContentsMargins(16, 15, 16, 15)
        layout.setSpacing(10)
        heading = label(title, "panelTitle")
        layout.addWidget(heading)
        if subtitle:
            layout.addWidget(label(subtitle, "muted"))
        return frame, layout

    def _build_live_page(self):
        page = QWidget()
        layout = QHBoxLayout(page)
        layout.setContentsMargins(0, 0, 0, 0)
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.setObjectName("consoleSplitter")
        splitter.setHandleWidth(8)
        splitter.setChildrenCollapsible(False)
        left_frame, left = self._panel("Приборы", "Выберите световой прибор или группу")
        left_frame.setMinimumWidth(175)
        left_frame.setMaximumWidth(430)
        self.fixture_tabs = QTabWidget()
        fixtures_page = QWidget()
        fixtures_layout = QVBoxLayout(fixtures_page)
        fixtures_layout.setContentsMargins(0, 6, 0, 0)
        fixtures_layout.setSpacing(8)
        self.fixture_list = QListWidget()
        self.fixture_list.setSelectionMode(QListWidget.SelectionMode.ExtendedSelection)
        self.fixture_list.itemSelectionChanged.connect(self._fixture_selection)
        self.fixture_list.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.fixture_list.customContextMenuRequested.connect(self._fixture_context_menu)
        fixtures_layout.addWidget(self.fixture_list, 1)
        fixtures_layout.addWidget(button("Добавить прибор", self._add_fixture))
        self.fixture_tabs.addTab(fixtures_page, "Приборы")
        self.fixture_tabs.addTab(self._build_gang_page(), "GANGS")
        left.addWidget(self.fixture_tabs, 1)
        splitter.addWidget(left_frame)

        center_frame = QWidget()
        middle = QVBoxLayout(center_frame)
        middle.setContentsMargins(0, 0, 0, 0)
        middle.setSpacing(12)
        self.live_stage_panel, stage_layout = self._panel("Сцена", "Планировка общая для live и snapshots")
        top = QHBoxLayout()
        self.live_label = label("LIVE  ·  НЕТ ВЫЗВАННОГО SNAPSHOT", "eyebrow")
        top.addWidget(self.live_label)
        top.addStretch(1)
        top.addWidget(button("Открыть сцену", lambda: self._select_page(1)))
        stage_layout.addLayout(top)
        self.live_stage = StageView()
        self.live_stage.setMinimumHeight(335)
        self.live_stage.objectChanged.connect(self._stage_action)
        self.live_stage.objectSelected.connect(self._stage_selected)
        stage_layout.addWidget(self.live_stage, 1)
        middle.addWidget(self.live_stage_panel, 1)

        center_frame.setMinimumWidth(300)
        splitter.addWidget(center_frame)

        controls, controls_layout = self._panel("Программатор", "Текущие значения")
        controls.setMinimumWidth(254)
        controls.setMaximumWidth(450)
        controls_scroll = QScrollArea()
        controls_scroll.setWidgetResizable(True)
        controls_scroll.setFrameShape(QFrame.Shape.NoFrame)
        controls_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        controls_scroll.setAutoFillBackground(False)
        controls_scroll.viewport().setAutoFillBackground(False)
        controls_scroll.viewport().setStyleSheet(f"background: {SURFACE};")
        controls_body = QWidget()
        controls_body.setStyleSheet(f"background: {SURFACE};")
        controls_body_layout = QVBoxLayout(controls_body)
        controls_body_layout.setContentsMargins(0, 0, 0, 0)
        controls_body_layout.setSpacing(7)
        controls_scroll.setWidget(controls_body)
        controls_layout.addWidget(controls_scroll, 1)
        self.control_titles = {}
        self.faders = {}
        for key, title, color in (("dimmer", "Яркость", "#f0f1f6"), ("r", "Красный", "#ff7586"),
                                  ("g", "Зелёный", "#71dda8"), ("b", "Синий", "#85a9ff"), ("w", "Белый", "#ffffff")):
            if key == "dimmer": controls_body_layout.addWidget(label("ЯРКОСТЬ", "eyebrow"))
            elif key == "r": controls_body_layout.addWidget(label("ЦВЕТ · RGB", "eyebrow"))
            elif key == "w": controls_body_layout.addWidget(label("БЕЛЫЙ КАНАЛ", "eyebrow"))
            group = QFrame()
            box = QVBoxLayout(group)
            box.setContentsMargins(0, 4, 0, 3)
            line = QHBoxLayout()
            line.addWidget(label(title, "muted"))
            value = label("0", "value")
            value.setMinimumWidth(26)
            value.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            self.control_titles[key] = value
            line.addStretch(1)
            line.addWidget(value)
            box.addLayout(line)
            slider = QSlider(Qt.Orientation.Horizontal)
            slider.setRange(0, 255)
            slider.setProperty("color", color)
            slider.setStyleSheet(f"QSlider::handle:horizontal {{ background: {color}; }}")
            slider.valueChanged.connect(lambda v, channel=key: self._set_channel(channel, v))
            slider.sliderPressed.connect(self._checkpoint)
            box.addWidget(slider)
            controls_body_layout.addWidget(group)
            self.faders[key] = slider
        controls_body_layout.addWidget(label("ЦВЕТОВОЙ КРУГ", "eyebrow"))
        self.color_wheel = ColorWheel()
        self.color_wheel.colorStarted.connect(self._checkpoint)
        self.color_wheel.colorSelected.connect(self._set_rgb_from_wheel)
        controls_body_layout.addWidget(self.color_wheel, 0, Qt.AlignmentFlag.AlignHCenter)
        self.color_swatch = QFrame()
        self.color_swatch.setObjectName("colorSwatch")
        self.color_swatch.setMinimumHeight(54)
        controls_body_layout.addWidget(self.color_swatch)
        palette_header = QHBoxLayout()
        palette_header.addWidget(label("ПАЛИТРА ЦВЕТОВ", "eyebrow"))
        palette_header.addStretch(1)
        self.save_color_button = button("+", self.save_current_color)
        self.save_color_button.setToolTip("Сохранить текущий цвет в палитру")
        palette_header.addWidget(self.save_color_button)
        controls_body_layout.addLayout(palette_header)
        self.color_palette_host = QWidget()
        self.color_palette_grid = QGridLayout(self.color_palette_host)
        self.color_palette_grid.setContentsMargins(0, 0, 0, 0)
        self.color_palette_grid.setSpacing(5)
        self.color_palette_scroll = QScrollArea()
        self.color_palette_scroll.setWidgetResizable(True)
        self.color_palette_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.color_palette_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.color_palette_scroll.setMaximumHeight(104)
        self.color_palette_scroll.setAutoFillBackground(False)
        self.color_palette_scroll.viewport().setAutoFillBackground(False)
        self.color_palette_scroll.viewport().setStyleSheet(f"background: {SURFACE};")
        self.color_palette_host.setStyleSheet(f"background: {SURFACE};")
        self.color_palette_scroll.setWidget(self.color_palette_host)
        controls_body_layout.addWidget(self.color_palette_scroll)
        self._refresh_color_palette()
        self.selected_name = label("PAR 01", "selectedName")
        controls_body_layout.addWidget(self.selected_name)
        connection_box = QFrame()
        connection_box.setObjectName("miniCard")
        connection_layout = QVBoxLayout(connection_box)
        connection_layout.setContentsMargins(9, 8, 9, 9)
        connection_layout.setSpacing(6)
        connection_layout.addWidget(label("DMX-ВЫХОД", "eyebrow"))
        self.port_combo = QComboBox()
        self.port_combo.setEditable(True)
        self.port_combo.setToolTip("Последовательный порт DMX-интерфейса, например COM3")
        connection_layout.addWidget(self.port_combo)
        port_row = QHBoxLayout()
        refresh = button("Порты")
        refresh.setToolTip("Обновить список COM-портов")
        refresh.clicked.connect(self._refresh_ports)
        port_row.addWidget(refresh)
        self.dmx_button = button("Подключить", primary=True)
        self.dmx_button.setToolTip("Подключить или отключить физический DMX-выход")
        self.dmx_button.clicked.connect(self._toggle_dmx)
        port_row.addWidget(self.dmx_button, 1)
        connection_layout.addLayout(port_row)
        self.dmx_refresh_button = button("Обновить DMX")
        self.dmx_refresh_button.setToolTip("Немедленно отправить текущие значения света в DMX-выход")
        self.dmx_refresh_button.clicked.connect(self._refresh_dmx)
        connection_layout.addWidget(self.dmx_refresh_button)
        controls_layout.addWidget(connection_box)
        splitter.addWidget(controls)
        splitter.setStretchFactor(0, 0); splitter.setStretchFactor(1, 1); splitter.setStretchFactor(2, 0)
        splitter.setSizes([270, 780, 300])
        self._connect_splitter(splitter)
        layout.addWidget(splitter)
        return page

    def _build_gang_page(self):
        page = QWidget()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(0, 6, 0, 0)
        layout.setSpacing(8)
        layout.addWidget(label("Связанные приборы", "eyebrow"))
        self.gang_list = QListWidget()
        self.gang_list.setSelectionMode(QListWidget.SelectionMode.SingleSelection)
        self.gang_list.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.gang_list.customContextMenuRequested.connect(self._gang_context_menu)
        layout.addWidget(self.gang_list, 1)
        create_button = button("Создать GANG", self.create_gang, primary=True)
        create_button.setToolTip("Создать GANG из выбранных приборов")
        layout.addWidget(create_button)
        add_button = button("Добавить в группу", self.add_selected_to_gang)
        add_button.setToolTip("Добавить выделенные приборы в выбранный GANG")
        layout.addWidget(add_button)
        remove_button = button("Убрать из группы", self.remove_selected_from_gang)
        remove_button.setToolTip("Убрать выделенные приборы из выбранного GANG")
        layout.addWidget(remove_button)
        scope_button = button("Настроить связь…", self.edit_gang_scope)
        scope_button.setToolTip("Выбрать каналы, которые будут двигаться вместе")
        layout.addWidget(scope_button)
        self.gang_isolate_button = button("Изолировать выбранные", self.toggle_gang_isolation)
        self.gang_isolate_button.setText("Изоляция выбранных")
        self.gang_isolate_button.setToolTip("Временно отключить выбранные приборы от GANG")
        layout.addWidget(self.gang_isolate_button)
        layout.addWidget(button("Удалить группу", self.remove_gang, danger=True))
        hint = label("Выберите приборы и создайте группу. Фейдеры сохраняют разницу уровней.", "muted")
        hint.setWordWrap(True)
        layout.addWidget(hint)
        return page

    def _selected_gang(self):
        if not hasattr(self, "gang_list") or not self.gang_list.currentItem():
            return None
        gang_id = self.gang_list.currentItem().data(Qt.ItemDataRole.UserRole)
        return next((gang for gang in self.show_data.get("gangs", []) if gang.get("id") == gang_id), None)

    def _refresh_gangs(self):
        if not hasattr(self, "gang_list"):
            return
        current_id = self.gang_list.currentItem().data(Qt.ItemDataRole.UserRole) if self.gang_list.currentItem() else None
        fixtures = {f["id"]: f for f in self.show_data.get("fixtures", [])}
        self.gang_list.blockSignals(True)
        self.gang_list.clear()
        for gang in self.show_data.get("gangs", []):
            members = [fixtures[fid]["name"] + (" · ISO" if fid in self.gang_isolated_ids else "")
                       for fid in gang.get("members", []) if fid in fixtures]
            scope_names = {"dimmer": "яркость", "r": "красный", "g": "зелёный", "b": "синий", "w": "белый"}
            scopes = ", ".join(scope_names[key] for key in gang.get("scope", []) if key in scope_names) or "нет каналов"
            item = QListWidgetItem(f"{gang.get('name', 'GANG')}\n{', '.join(members)}\nСвязь: {scopes}")
            item.setData(Qt.ItemDataRole.UserRole, gang["id"])
            self.gang_list.addItem(item)
            if gang["id"] == current_id:
                self.gang_list.setCurrentItem(item)
        self.gang_list.blockSignals(False)

    def create_gang(self):
        selected = [f for f in self.show_data.get("fixtures", []) if f["id"] in self.selected_fixture_ids]
        if len(selected) < 2:
            QMessageBox.information(self, "Создать GANG", "Выберите не менее двух приборов во вкладке «Приборы».")
            return
        occupied = {fid for gang in self.show_data.get("gangs", []) for fid in gang.get("members", [])}
        if any(f["id"] in occupied for f in selected):
            QMessageBox.warning(self, "Создать GANG", "Каждый прибор может входить только в один GANG. Сначала уберите его из текущей группы.")
            return
        name, accepted = QInputDialog.getText(self, "Создать GANG", "Название группы:", text=f"GANG {len(self.show_data.get('gangs', [])) + 1}")
        if not accepted or not name.strip():
            return
        self._checkpoint()
        gang = {"id": new_id(), "name": name.strip(), "members": [f["id"] for f in selected],
                "scope": ["dimmer", "r", "g", "b", "w"]}
        self.show_data.setdefault("gangs", []).append(gang)
        self.gang_isolated_ids.difference_update(gang["members"])
        self.dirty = True
        self._refresh_gangs(); self._refresh_fixture_rows()

    def add_selected_to_gang(self):
        gang = self._selected_gang()
        selected = [f["id"] for f in self.show_data.get("fixtures", []) if f["id"] in self.selected_fixture_ids]
        if not gang or not selected:
            QMessageBox.information(self, "GANG", "Выберите группу и приборы для добавления.")
            return
        used_elsewhere = {fid for other in self.show_data.get("gangs", []) if other["id"] != gang["id"] for fid in other.get("members", [])}
        if any(fid in used_elsewhere for fid in selected):
            QMessageBox.warning(self, "GANG", "Один или несколько приборов уже входят в другую группу.")
            return
        additions = [fid for fid in selected if fid not in gang.setdefault("members", [])]
        if additions:
            self._checkpoint(); gang["members"].extend(additions)
            self.gang_isolated_ids.difference_update(additions); self.dirty = True
            self._refresh_gangs(); self._refresh_fixture_rows()

    def remove_selected_from_gang(self):
        gang = self._selected_gang()
        selected = self.selected_fixture_ids
        if not gang or not selected:
            QMessageBox.information(self, "GANG", "Выберите группу и приборы, которые нужно убрать.")
            return
        members = [fid for fid in gang.get("members", []) if fid not in selected]
        if members == gang.get("members", []):
            return
        self._checkpoint(); gang["members"] = members
        self.gang_isolated_ids.difference_update(selected); self.dirty = True
        if len(members) < 2:
            self.show_data["gangs"] = [item for item in self.show_data["gangs"] if item["id"] != gang["id"]]
        self._refresh_gangs(); self._refresh_fixture_rows()

    def remove_gang(self):
        gang = self._selected_gang()
        if not gang:
            return
        self._checkpoint()
        self.gang_isolated_ids.difference_update(gang.get("members", []))
        self.show_data["gangs"] = [item for item in self.show_data["gangs"] if item["id"] != gang["id"]]
        self.dirty = True; self._refresh_gangs(); self._refresh_fixture_rows()

    def edit_gang_scope(self):
        gang = self._selected_gang()
        if not gang:
            QMessageBox.information(self, "GANG", "Сначала выберите группу.")
            return
        dialog = QDialog(self); dialog.setWindowTitle(f"Каналы связи · {gang.get('name', 'GANG')}")
        layout = QVBoxLayout(dialog)
        layout.addWidget(label("При движении фейдера связанные приборы изменяются на одинаковый шаг."))
        names = [("dimmer", "Яркость"), ("r", "Красный"), ("g", "Зелёный"), ("b", "Синий"), ("w", "Белый")]
        checks = {}
        for key, title in names:
            checks[key] = QCheckBox(title); checks[key].setChecked(key in gang.get("scope", [])); layout.addWidget(checks[key])
        actions = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        actions.accepted.connect(dialog.accept); actions.rejected.connect(dialog.reject); layout.addWidget(actions)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            scope = [key for key, _ in names if checks[key].isChecked()]
            if scope != gang.get("scope", []):
                self._checkpoint(); gang["scope"] = scope; self.dirty = True; self._refresh_gangs()

    def toggle_gang_isolation(self):
        selected = [f["id"] for f in self.show_data.get("fixtures", []) if f["id"] in self.selected_fixture_ids]
        gang_ids = {fid for gang in self.show_data.get("gangs", []) for fid in gang.get("members", [])}
        eligible = [fid for fid in selected if fid in gang_ids]
        if not eligible:
            QMessageBox.information(self, "Изоляция GANG", "Выбранные приборы не входят в GANG.")
            return
        for fid in eligible:
            if fid in self.gang_isolated_ids: self.gang_isolated_ids.remove(fid)
            else: self.gang_isolated_ids.add(fid)
        self._refresh_gangs(); self._refresh_fixture_rows()

    def _gang_context_menu(self, pos):
        item = self.gang_list.itemAt(pos)
        if item: self.gang_list.setCurrentItem(item)
        menu = QMenu(self)
        menu.addAction("Настроить каналы…", self.edit_gang_scope)
        menu.addAction("Изолировать выбранные приборы", self.toggle_gang_isolation)
        menu.addSeparator(); menu.addAction("Удалить GANG", self.remove_gang)
        menu.exec(self.gang_list.mapToGlobal(pos))

    def _refresh_fixture_rows(self):
        if not hasattr(self, "fixture_list"): return
        self.fixture_list.blockSignals(True); self.fixture_list.clear()
        member_of = {fid: gang.get("name", "GANG") for gang in self.show_data.get("gangs", []) for fid in gang.get("members", [])}
        for fixture in self.show_data.get("fixtures", []):
            status = f" · {member_of[fixture['id']]}" if fixture["id"] in member_of else ""
            if fixture["id"] in self.gang_isolated_ids: status += " · ISO"
            item = QListWidgetItem(f"{fixture['name']}     ·     {fixture['address']:03d}{status}")
            item.setData(Qt.ItemDataRole.UserRole, fixture["id"]); self.fixture_list.addItem(item)
            if fixture["id"] in self.selected_fixture_ids: item.setSelected(True)
        self.fixture_list.blockSignals(False)

    @staticmethod
    def _get_preferences_path():
        base = Path(os.environ.get("APPDATA", Path.home() / ".config"))
        return base / "OLEG" / "preferences.json"

    def _load_ui_scale(self):
        try:
            data = json.loads(self._preferences_path.read_text(encoding="utf-8"))
            scale = float(data.get("ui_scale", 1.0)) if isinstance(data, dict) else 1.0
            return max(.75, min(1.45, scale))
        except (OSError, ValueError, TypeError):
            return 1.0

    def _load_splitter_sizes(self):
        try:
            data = json.loads(self._preferences_path.read_text(encoding="utf-8"))
            saved = data.get("splitters", {}) if isinstance(data, dict) else {}
            return {key: values for key, values in saved.items()
                    if isinstance(key, str) and isinstance(values, list) and len(values) >= 2
                    and all(isinstance(value, (int, float)) and math.isfinite(value) and value > 0 for value in values)}
        except (OSError, ValueError, TypeError):
            return {}

    def _connect_splitter(self, splitter):
        splitter.splitterMoved.connect(lambda _position, _index: self.layout_preferences_timer.start())

    def _restore_splitter_sizes(self):
        for splitter in self.findChildren(QSplitter):
            values = self._saved_splitter_sizes.get(splitter.objectName())
            if values and len(values) == splitter.count():
                splitter.setSizes([round(value * 1000) for value in values])

    def _splitter_ratios(self):
        result = {}
        for splitter in self.findChildren(QSplitter):
            sizes = splitter.sizes()
            total = sum(sizes)
            if splitter.objectName() and len(sizes) >= 2 and total:
                result[splitter.objectName()] = [round(size / total, 5) for size in sizes]
        return result

    def _capture_ui_metrics(self):
        self._ui_scale_widgets = []
        for widget in self.findChildren(QWidget):
            minimum, maximum = widget.minimumSize(), widget.maximumSize()
            self._ui_scale_widgets.append((widget, minimum, maximum))
        layouts = list(self.findChildren(QLayout))
        root_layout = self.centralWidget().layout() if self.centralWidget() else None
        if root_layout and root_layout not in layouts:
            layouts.append(root_layout)
        self._ui_scale_layouts = [(layout, layout.contentsMargins(), layout.spacing()) for layout in layouts]

    def _apply_ui_scale(self, scale, persist=True):
        self.ui_scale = max(.75, min(1.45, float(scale)))
        for widget, minimum, maximum in self._ui_scale_widgets:
            min_w = round(minimum.width() * self.ui_scale) if minimum.width() < 100000 else minimum.width()
            min_h = round(minimum.height() * self.ui_scale) if minimum.height() < 100000 else minimum.height()
            max_w = round(maximum.width() * self.ui_scale) if maximum.width() < 100000 else maximum.width()
            max_h = round(maximum.height() * self.ui_scale) if maximum.height() < 100000 else maximum.height()
            widget.setMinimumSize(min_w, min_h)
            widget.setMaximumSize(max_w, max_h)
        ordinary_button_height = max(30, round(34 * self.ui_scale))
        important_button_height = max(40, round(40 * self.ui_scale))
        for widget in self.findChildren(QPushButton):
            is_important = (widget is getattr(self, "blackout_button", None)
                            or widget.text().strip().casefold() == "fire")
            target_height = important_button_height if is_important else ordinary_button_height
            widget.setMinimumHeight(max(widget.minimumHeight(), target_height))
        field_height = max(32, round(36 * self.ui_scale))
        for widget_type in (QComboBox, QDoubleSpinBox, QLineEdit, QSpinBox):
            for widget in self.findChildren(widget_type):
                widget.setMinimumHeight(max(widget.minimumHeight(), field_height))
        slider_height = max(24, round(28 * self.ui_scale))
        for widget in self.findChildren(QSlider):
            widget.setMinimumHeight(max(widget.minimumHeight(), slider_height))
        if hasattr(self, "color_wheel"):
            wheel_diameter = max(112, round(160 * self.ui_scale))
            self.color_wheel.setMinimumSize(wheel_diameter, wheel_diameter)
            self.color_wheel.updateGeometry()
        for layout, margins, spacing in self._ui_scale_layouts:
            layout.setContentsMargins(*(round(value * self.ui_scale) for value in
                                        (margins.left(), margins.top(), margins.right(), margins.bottom())))
            if spacing >= 0:
                layout.setSpacing(round(spacing * self.ui_scale))
        scaled_stylesheet = re.sub(
            r"(?<![A-Za-z])(\d+(?:\.\d+)?)(px|pt)\b",
            lambda match: f"{float(match.group(1)) * self.ui_scale:g}{match.group(2)}",
            self._stylesheet(),
        )
        slider_handle_width = max(16, round(18 * self.ui_scale))
        scaled_stylesheet = re.sub(
            r"(QSlider::handle:horizontal\s*\{\s*width:\s*)\d+(?:\.\d+)?px",
            lambda match: f"{match.group(1)}{slider_handle_width}px",
            scaled_stylesheet,
        )
        self.setStyleSheet(scaled_stylesheet)
        screen = self.screen() or QApplication.primaryScreen()
        available = screen.availableGeometry() if screen else None
        minimum_width = round(1180 * self.ui_scale)
        minimum_height = round(700 * self.ui_scale)
        requested_width = round(1500 * self.ui_scale)
        requested_height = round(920 * self.ui_scale)
        if available:
            minimum_width = min(minimum_width, available.width())
            minimum_height = min(minimum_height, available.height())
            requested_width = min(requested_width, available.width())
            requested_height = min(requested_height, available.height())
        self.setMinimumSize(minimum_width, minimum_height)
        if not self.isMaximized():
            self.resize(requested_width, requested_height)
        self._update_header_layout()
        if hasattr(self, "ui_scale_picker"):
            self.ui_scale_picker.blockSignals(True)
            index = min(range(self.ui_scale_picker.count()),
                        key=lambda item: abs(self.ui_scale_picker.itemData(item) - self.ui_scale))
            self.ui_scale_picker.setCurrentIndex(index)
            self.ui_scale_picker.blockSignals(False)
        if hasattr(self, "editor_stage"):
            self.refresh_stage_views()
        if persist and hasattr(self, "_preferences_path"):
            self._save_preferences()

    def _ui_scale_picked(self, index):
        if index >= 0:
            self._apply_ui_scale(self.ui_scale_picker.itemData(index))

    def _step_ui_scale(self, amount):
        choices = (0.75, 0.85, 1.0, 1.15, 1.30, 1.45)
        current = min(range(len(choices)), key=lambda item: abs(choices[item] - self.ui_scale))
        self._apply_ui_scale(choices[max(0, min(len(choices) - 1, current + amount))])

    def _setup_ui_scale_shortcuts(self):
        for sequence, amount in (("Ctrl++", 1), ("Ctrl+=", 1), ("Ctrl+-", -1), ("Ctrl+0", 0)):
            shortcut = QShortcut(QKeySequence(sequence), self)
            shortcut.activated.connect(lambda a=amount: self._apply_ui_scale(1.0) if a == 0 else self._step_ui_scale(a))
            setattr(self, f"_scale_shortcut_{sequence.replace('+', 'plus').replace('-', 'minus')}", shortcut)

    def _load_saved_colors(self):
        paths = [self._preferences_path]
        legacy_path = self._preferences_path.parent.parent / "LUMA DMX" / "preferences.json"
        if legacy_path not in paths: paths.append(legacy_path)
        for path in paths:
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError, TypeError):
                continue
            items = data.get("saved_colors", []) if isinstance(data, dict) else []
            result = []
            for item in items if isinstance(items, list) else []:
                values = item.get("rgbw") if isinstance(item, dict) else None
                if (isinstance(item, dict) and isinstance(item.get("name"), str) and item["name"].strip()
                        and isinstance(values, dict)
                        and all(type(values.get(key)) is int and 0 <= values[key] <= 255 for key in ("r", "g", "b", "w"))):
                    result.append({"name": item["name"].strip(), "rgbw": {key: values[key] for key in ("r", "g", "b", "w")}})
            if result:
                return result
        return []

    def _save_preferences(self):
        try:
            self._preferences_path.parent.mkdir(parents=True, exist_ok=True)
            try:
                preferences = json.loads(self._preferences_path.read_text(encoding="utf-8"))
                if not isinstance(preferences, dict): preferences = {}
            except (OSError, ValueError, TypeError):
                preferences = {}
            preferences["saved_colors"] = self.saved_colors
            preferences["ui_scale"] = self.ui_scale
            preferences["splitters"] = self._splitter_ratios()
            temporary = self._preferences_path.with_suffix(".tmp")
            temporary.write_text(json.dumps(preferences, ensure_ascii=False, indent=2), encoding="utf-8")
            temporary.replace(self._preferences_path)
        except OSError as exc:
            self.status_bar.setText(f"Не удалось сохранить палитру · {exc}")

    def _refresh_color_palette(self):
        if not hasattr(self, "color_palette_grid"):
            return
        while self.color_palette_grid.count():
            item = self.color_palette_grid.takeAt(0)
            if item.widget(): item.widget().deleteLater()
        if not self.saved_colors:
            empty = label("Пока нет сохранённых цветов", "muted")
            self.color_palette_grid.addWidget(empty, 0, 0, 1, 2)
            return
        for index, saved in enumerate(self.saved_colors):
            values = saved["rgbw"]
            white = round(values["w"] * .72)
            rgb = [min(255, values[key] + white) for key in ("r", "g", "b")]
            swatch = QColor(*rgb)
            foreground = "#12141a" if (swatch.red() * .299 + swatch.green() * .587 + swatch.blue() * .114) > 150 else "#ffffff"
            chip = button(saved["name"][:12], lambda _checked=False, i=index: self.apply_saved_color(i))
            chip.setToolTip(f"{saved['name']} · нажмите для применения, правая кнопка для удаления")
            chip.setStyleSheet(f"QPushButton {{ background: {swatch.name()}; color: {foreground}; border: 1px solid {LINE}; padding: 5px; }} QPushButton:hover {{ border: 2px solid {ACCENT}; }}")
            chip.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
            chip.customContextMenuRequested.connect(lambda pos, i=index, widget=chip: self._saved_color_menu(i, widget, pos))
            self.color_palette_grid.addWidget(chip, index // 2, index % 2)

    def save_current_color(self):
        selected = [fixture for fixture in self.show_data.get("fixtures", []) if fixture["id"] in self.selected_fixture_ids]
        if not selected:
            QMessageBox.information(self, "Палитра цветов", "Сначала выберите прибор.")
            return
        name, accepted = QInputDialog.getText(self, "Сохранить цвет", "Название цвета:", text=f"Цвет {len(self.saved_colors) + 1}")
        if not accepted or not name.strip(): return
        look = selected[0].get("look", {})
        self.saved_colors.append({"name": name.strip(), "rgbw": {key: max(0, min(255, int(look.get(key, 0)))) for key in ("r", "g", "b", "w")}})
        self._save_preferences(); self._refresh_color_palette()

    def apply_saved_color(self, index):
        if not 0 <= index < len(self.saved_colors): return
        selected_ids = set(self.selected_fixture_ids)
        selected = [fixture for fixture in self.show_data.get("fixtures", []) if fixture["id"] in selected_ids]
        if not selected: return
        self._cancel_fade()
        self._checkpoint()
        reference = selected[0].setdefault("look", blank_look())
        values = self.saved_colors[index]["rgbw"]
        for key in ("r", "g", "b", "w"):
            targets = selected
            gang = next((item for item in self.show_data.get("gangs", [])
                         if key in item.get("scope", []) and selected_ids
                         and selected_ids.issubset(set(item.get("members", [])))), None)
            if gang and not selected_ids.intersection(self.gang_isolated_ids):
                targets = [f for f in self.show_data["fixtures"] if f["id"] in gang.get("members", []) and f["id"] not in self.gang_isolated_ids]
            delta = int(values[key]) - int(reference.get(key, 0))
            processed = set()
            for fixture in targets:
                mirror_id = fixture.get("mirror_group_id")
                token = mirror_id or fixture["id"]
                if token in processed: continue
                processed.add(token)
                look = fixture.setdefault("look", blank_look())
                new_value = max(0, min(255, int(look.get(key, 0)) + delta))
                look[key] = new_value
                if mirror_id:
                    for mirror in self.show_data["fixtures"]:
                        if mirror.get("mirror_group_id") == mirror_id:
                            mirror.setdefault("look", blank_look())[key] = new_value
        if int(reference.get("dimmer", 0)) == 0:
            targets = selected
            gang = next((item for item in self.show_data.get("gangs", [])
                         if "dimmer" in item.get("scope", []) and selected_ids
                         and selected_ids.issubset(set(item.get("members", [])))), None)
            if gang and not selected_ids.intersection(self.gang_isolated_ids):
                targets = [f for f in self.show_data["fixtures"] if f["id"] in gang.get("members", []) and f["id"] not in self.gang_isolated_ids]
            delta = 255 - int(reference.get("dimmer", 0))
            for fixture in targets:
                look = fixture.setdefault("look", blank_look())
                look["dimmer"] = max(0, min(255, int(look.get("dimmer", 0)) + delta))
        self.dirty = True
        self._fixture_selection_from_ids(); self._update_color_swatch()
        self.refresh_stage_views(); self._send_dmx()

    def _saved_color_menu(self, index, widget, pos):
        if not 0 <= index < len(self.saved_colors): return
        menu = QMenu(self)
        menu.addAction("Применить", lambda: self.apply_saved_color(index))
        menu.addAction("Удалить из палитры", lambda: self.remove_saved_color(index))
        menu.exec(widget.mapToGlobal(pos))

    def remove_saved_color(self, index):
        if not 0 <= index < len(self.saved_colors): return
        self.saved_colors.pop(index); self._save_preferences(); self._refresh_color_palette()

    def _update_color_swatch(self):
        if not hasattr(self, "color_swatch"): return
        fixtures = [f for f in self.show_data.get("fixtures", []) if f["id"] in self.selected_fixture_ids]
        if not fixtures:
            self.color_swatch.setStyleSheet(f"QFrame#colorSwatch {{ background: {SURFACE_2}; border: 1px solid {LINE}; border-radius: 10px; }}")
            if hasattr(self, "color_wheel"):
                self.color_wheel.setColor("#ffffff")
            return
        look = fixtures[0].get("look", {})
        white = round(int(look.get("w", 0)) * .72)
        color = QColor(*(min(255, int(look.get(key, 0)) + white) for key in ("r", "g", "b")))
        self.color_swatch.setStyleSheet(f"QFrame#colorSwatch {{ background: {color.name()}; border: 1px solid {LINE}; border-radius: 10px; }}")
        if hasattr(self, "color_wheel"):
            self.color_wheel.setColor(QColor(*(int(look.get(key, 0)) for key in ("r", "g", "b"))))

    def _set_rgb_from_wheel(self, color):
        for key, value in zip(("r", "g", "b"), color.getRgb()[:3]):
            self.faders[key].setValue(value)

    def _build_stage_page(self):
        page = QWidget()
        layout = QHBoxLayout(page)
        layout.setContentsMargins(0, 0, 0, 0)
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.setObjectName("stageEditorSplitter")
        splitter.setHandleWidth(8)
        splitter.setChildrenCollapsible(False)
        editor, center = self._panel("План сцены", "Перетаскивайте формы · выделяйте рамкой для совместного движения · масштабируйте угол или колесо")
        editor.setMinimumWidth(330)
        self.editor_stage = StageView(zoom_enabled=True)
        self.editor_stage.setMinimumHeight(430)
        self.editor_stage.objectChanged.connect(self._stage_action)
        self.editor_stage.objectSelected.connect(self._stage_selected)
        self.editor_stage.selectionChanged.connect(self._sync_stage_inspector)
        top = QHBoxLayout()
        self.stage_width = QSpinBox(); self.stage_width.setRange(1, 100); self.stage_width.setSuffix(" м ширина")
        self.stage_depth = QSpinBox(); self.stage_depth.setRange(1, 100); self.stage_depth.setSuffix(" м глубина")
        self.stage_width.valueChanged.connect(self._set_stage_dimensions)
        self.stage_depth.valueChanged.connect(self._set_stage_dimensions)
        top.addWidget(self.stage_width); top.addWidget(self.stage_depth)
        top.addWidget(label("ПЛАН", "eyebrow"))
        self.stage_layout_picker = QComboBox()
        self.stage_layout_picker.setMinimumWidth(140)
        self.stage_layout_picker.currentIndexChanged.connect(self._stage_layout_selected)
        top.addWidget(self.stage_layout_picker)
        top.addWidget(button("Сохранить как…", self._save_stage_layout_as))
        self.delete_stage_layout_button = button("Удалить план", self._delete_stage_layout, danger=True)
        top.addWidget(self.delete_stage_layout_button)
        self.stage_symmetry = QCheckBox("Симметрия")
        self.stage_symmetry.setToolTip("Новые формы будут создаваться зеркальной парой относительно центра сцены")
        top.addWidget(self.stage_symmetry)
        top.addStretch(1)
        top.addWidget(label("МАСШТАБ", "eyebrow"))
        top.addWidget(button("−", self.editor_stage.zoom_out))
        self.zoom_reset_button = button("100%", self.editor_stage.reset_zoom)
        self.zoom_reset_button.setToolTip("Вернуть масштаб сцены к размеру окна")
        self.editor_stage.zoomChanged.connect(lambda factor: self.zoom_reset_button.setText(f"{round(factor * 100)}%"))
        top.addWidget(self.zoom_reset_button)
        top.addWidget(button("+", self.editor_stage.zoom_in))
        center.addLayout(top)
        center.addWidget(self.editor_stage, 1)
        palette = QHBoxLayout()
        presets = (("Вокал", "musician", "vocal"), ("Гитара", "musician", "guitar"),
                   ("Бас", "musician", "bass"),
                   ("Клавиши", "musician", "keys"), ("Ударные", "musician", "drums"),
                   ("Подпись", "label", None), ("Форма", "rect", None), ("Круг", "circle", None),
                   ("Колонна", "column", None))
        for title, kind, instrument in presets:
            drag_kind = f"{kind}:{instrument}" if instrument else kind
            tool = PaletteButton(title, drag_kind)
            tool.clicked.connect(lambda _checked=False, k=kind, i=instrument: self._stage_action({"add": k, "instrument": i, "x": .45, "y": .42}))
            palette.addWidget(tool)
        palette.addStretch(1)
        center.addLayout(palette)
        splitter.addWidget(editor)

        inspector, inspector_layout = self._panel("Выбранный объект", "Настройте ориентир сцены")
        inspector.setMinimumWidth(225)
        inspector.setMaximumWidth(460)
        self.stage_name = QLineEdit()
        self.stage_name.setPlaceholderText("Название")
        self.stage_name.editingFinished.connect(self._apply_stage_inspector)
        inspector_layout.addWidget(label("НАЗВАНИЕ", "eyebrow"))
        inspector_layout.addWidget(self.stage_name)
        inspector_layout.addWidget(label("ЦВЕТ · RGB", "eyebrow"))
        self.stage_color_sliders = {}
        self.stage_color_values = {}
        for key, title, tint in (("r", "Красный", "#ff7586"), ("g", "Зелёный", "#71dda8"), ("b", "Синий", "#85a9ff")):
            color_row = QHBoxLayout()
            color_row.addWidget(label(title, "muted"))
            color_row.addStretch(1)
            value = label("0", "value")
            self.stage_color_values[key] = value
            color_row.addWidget(value)
            inspector_layout.addLayout(color_row)
            slider = QSlider(Qt.Orientation.Horizontal); slider.setRange(0, 255); slider.setProperty("color", tint)
            slider.setStyleSheet(f"QSlider::handle:horizontal {{ background: {tint}; }}")
            slider.valueChanged.connect(lambda v, k=key, text=value: (text.setText(str(v)), self._apply_stage_inspector()))
            inspector_layout.addWidget(slider)
            self.stage_color_sliders[key] = slider
        size_row = QHBoxLayout()
        self.object_width = QDoubleSpinBox(); self.object_width.setRange(.02, .98); self.object_width.setSingleStep(.02); self.object_width.setSuffix(" шир.")
        self.object_height = QDoubleSpinBox(); self.object_height.setRange(.02, .98); self.object_height.setSingleStep(.02); self.object_height.setSuffix(" выс.")
        self.object_diagonal = QDoubleSpinBox(); self.object_diagonal.setRange(.02, 1.39); self.object_diagonal.setSingleStep(.02); self.object_diagonal.setSuffix(" диаг.")
        self.object_rotation = QDoubleSpinBox(); self.object_rotation.setRange(-180, 180); self.object_rotation.setSingleStep(5); self.object_rotation.setSuffix("°")
        self.beam_size = QDoubleSpinBox(); self.beam_size.setRange(.25, 2.0); self.beam_size.setSingleStep(.1); self.beam_size.setSuffix(" ширина луча")
        self.beam_length = QDoubleSpinBox(); self.beam_length.setRange(.45, 5); self.beam_length.setSingleStep(.1); self.beam_length.setSuffix(" длина луча")
        self.object_width.valueChanged.connect(self._apply_stage_inspector)
        self.object_height.valueChanged.connect(self._apply_stage_inspector)
        self.object_diagonal.valueChanged.connect(self._apply_stage_diagonal)
        self.object_rotation.valueChanged.connect(self._apply_stage_inspector)
        self.beam_size.valueChanged.connect(self._apply_stage_inspector)
        self.beam_length.valueChanged.connect(self._apply_stage_inspector)
        size_row.addWidget(self.object_width); size_row.addWidget(self.object_height)
        inspector_layout.addWidget(label("РАЗМЕР · ДИАГОНАЛЬ · ПОВОРОТ", "eyebrow"))
        inspector_layout.addLayout(size_row)
        transform_row = QHBoxLayout()
        transform_row.addWidget(self.object_diagonal); transform_row.addWidget(self.object_rotation)
        inspector_layout.addLayout(transform_row)
        inspector_layout.addWidget(label("СВЕТ ПРОЖЕКТОРА", "eyebrow"))
        inspector_layout.addWidget(self.beam_size)
        inspector_layout.addWidget(self.beam_length)
        inspector_layout.addStretch(1)
        self.delete_stage_button = button("Удалить объект", self._delete_stage, danger=True)
        inspector_layout.addWidget(self.delete_stage_button)
        inspector.setObjectName("stageInspectorPanel")
        inspector_scroll = QScrollArea()
        inspector_scroll.setObjectName("stageInspectorScroll")
        inspector_scroll.setWidgetResizable(True)
        inspector_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        inspector_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        inspector_scroll.setFrameShape(QFrame.Shape.NoFrame)
        inspector_scroll.setMinimumWidth(245)
        inspector_scroll.setMaximumWidth(460)
        inspector_scroll.setWidget(inspector)
        splitter.addWidget(inspector_scroll)
        splitter.setStretchFactor(0, 1); splitter.setStretchFactor(1, 0)
        splitter.setSizes([950, 280])
        self._connect_splitter(splitter)
        layout.addWidget(splitter)
        return page

    def _build_cues_page(self):
        page = QWidget()
        layout = QHBoxLayout(page); layout.setContentsMargins(0, 0, 0, 0)
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.setObjectName("snapshotsSplitter")
        splitter.setHandleWidth(8)
        splitter.setChildrenCollapsible(False)
        items, items_layout = self._panel("Snapshots", "Состояния света для вызова по ходу шоу")
        items.setMinimumWidth(190)
        items.setMaximumWidth(470)
        self.cue_list = QListWidget()
        self.cue_list.currentItemChanged.connect(self._cue_selection)
        self.cue_list.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.cue_list.customContextMenuRequested.connect(self._cue_context_menu)
        items_layout.addWidget(self.cue_list, 1)
        row = QHBoxLayout()
        row.addWidget(button("Новый", self._add_cue, primary=True))
        row.addWidget(button("Настроить", self._edit_cue))
        row.addWidget(button("Удалить", self._delete_cue, danger=True))
        items_layout.addLayout(row)
        self.auto_next = QPushButton("После FIRE выбрать следующий")
        self.auto_next.setCheckable(True)
        self.auto_next.setToolTip("После вызова автоматически выбрать следующий snapshot для предпросмотра")
        items_layout.addWidget(self.auto_next)
        cue_actions = QHBoxLayout()
        cue_actions.addWidget(button("FIRE", self.fire_cue, danger=True))
        cue_actions.addWidget(button("Назад", self.previous_cue))
        items_layout.addLayout(cue_actions)
        splitter.addWidget(items)
        preview, preview_layout = self._panel("Сцены шоу", "Общий план сцены · текущее LIVE-состояние и выбранный предпросмотр")
        preview.setMinimumWidth(310)
        self.cue_preview_info = label("Выберите snapshot для предпросмотра", "muted")
        preview_layout.addWidget(self.cue_preview_info)
        scene_columns = QVBoxLayout()
        scene_columns.setSpacing(10)
        live_scene_column = QVBoxLayout()
        self.cue_live_scene_caption = label("● LIVE · НЕТ ВЫЗВАННОГО SNAPSHOT", "liveScene")
        live_scene_column.addWidget(self.cue_live_scene_caption)
        self.cue_live_stage = StageView()
        self.cue_live_stage.setMinimumSize(340, 230)
        self.cue_live_stage.objectSelected.connect(self._stage_selected)
        live_scene_column.addWidget(self.cue_live_stage, 1)
        scene_columns.addLayout(live_scene_column, 1)
        preview_scene_column = QVBoxLayout()
        self.cue_preview_scene_caption = label("◉ ПРЕДПРОСМОТР · НЕ ВЫБРАН", "previewScene")
        preview_scene_column.addWidget(self.cue_preview_scene_caption)
        self.cue_stage = StageView()
        self.cue_stage.setMinimumSize(340, 230)
        self.cue_stage.objectSelected.connect(self._stage_selected)
        preview_scene_column.addWidget(self.cue_stage, 1)
        scene_columns.addLayout(preview_scene_column, 1)
        preview_layout.addLayout(scene_columns, 1)
        splitter.addWidget(preview)
        splitter.setStretchFactor(0, 0); splitter.setStretchFactor(1, 1)
        splitter.setSizes([300, 950])
        self._connect_splitter(splitter)
        layout.addWidget(splitter)
        return page

    def _build_patch_page(self):
        page = QWidget()
        layout = QVBoxLayout(page); layout.setContentsMargins(0, 0, 0, 0)
        frame, content = self._panel("Патч", "Управление адресами и группами приборов")
        self.patch_table = QTableWidget(0, 4)
        self.patch_table.setHorizontalHeaderLabels(["Прибор", "Адрес", "Группа", "Профиль"])
        self.patch_table.horizontalHeader().setStretchLastSection(True)
        self.patch_table.verticalHeader().setVisible(False)
        self.patch_table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.patch_table.setSelectionMode(QTableWidget.SelectionMode.ExtendedSelection)
        self.patch_table.itemSelectionChanged.connect(self._patch_selection)
        self.patch_table.itemChanged.connect(self._patch_item_changed)
        content.addWidget(self.patch_table, 1)
        row = QHBoxLayout()
        row.addWidget(button("Добавить прибор", self._add_fixture, primary=True))
        row.addWidget(button("Удалить выбранные", self._delete_fixtures, danger=True))
        row.addStretch(1)
        content.addLayout(row)
        layout.addWidget(frame)
        return page

    def _build_bridge_page(self):
        page = QWidget()
        layout = QVBoxLayout(page); layout.setContentsMargins(0, 0, 0, 0)
        frame, content = self._panel("Связи и playback", "Сетевые адаптеры не блокируют локальное управление DMX")

        pp_card = QFrame(); pp_card.setObjectName("miniCard")
        pp_layout = QVBoxLayout(pp_card)
        pp_layout.setContentsMargins(14, 12, 14, 14); pp_layout.setSpacing(9)
        pp_heading = QHBoxLayout()
        pp_heading.addWidget(label("ProPresenter API", "panelTitle"))
        pp_heading.addStretch(1)
        self.pp_badge = label("НЕ ПРОВЕРЕНО", "badge")
        pp_heading.addWidget(self.pp_badge)
        pp_layout.addLayout(pp_heading)
        pp_description = label(
            "API доступен в ProPresenter 7.9 и новее. Включите Network в Preferences и возьмите адрес и порт из этой вкладки. "
            "API Documentation там же показывает доступные запросы. Проверка ниже проверяет только TCP-порт.", "muted")
        pp_description.setWordWrap(True)
        pp_layout.addWidget(pp_description)

        bridge_row = QHBoxLayout(); bridge_row.setSpacing(8)
        self.pp_host = QLineEdit("127.0.0.1")
        self.pp_host.setPlaceholderText("Адрес ProPresenter")
        self.pp_host.setToolTip("Имя компьютера или IP-адрес из настроек ProPresenter")
        self.pp_port = QSpinBox(); self.pp_port.setRange(0, 65535)
        self.pp_port.setSpecialValueText("Порт из Preferences")
        self.pp_port.setValue(0); self.pp_port.setMaximumWidth(190)
        self.pp_port.setToolTip("Порт указан в ProPresenter → Preferences → Network")
        self.pp_probe_button = button("Проверить порт", self._check_prop_presenter, primary=True)
        bridge_row.addWidget(self.pp_host, 1)
        bridge_row.addWidget(self.pp_port)
        bridge_row.addWidget(self.pp_probe_button)
        pp_layout.addLayout(bridge_row)
        self.pp_status = label("Укажите порт из настроек ProPresenter, затем проверьте соединение.", "muted")
        pp_layout.addWidget(self.pp_status)
        self.pp_probe_timer = QTimer(self)
        self.pp_probe_timer.setSingleShot(True)
        self.pp_probe_timer.timeout.connect(self._propresenter_port_timeout)
        content.addWidget(pp_card)

        line = QFrame(); line.setFrameShape(QFrame.Shape.HLine); line.setObjectName("separator"); content.addWidget(line)
        playback_card = QFrame(); playback_card.setObjectName("miniCard")
        playback_layout = QVBoxLayout(playback_card)
        playback_layout.setContentsMargins(14, 12, 14, 14); playback_layout.setSpacing(8)
        playback_layout.addWidget(label("Playback", "panelTitle"))
        playback_description = label(
            "Подключение к воспроизведению будет отдельным адаптером: оно не должно менять snapshots "
            "или останавливать DMX. Выбор конкретного проигрывателя и протокола остаётся отдельным этапом.", "muted")
        playback_description.setWordWrap(True)
        playback_layout.addWidget(playback_description)
        content.addWidget(playback_card)
        content.addWidget(label("Локальная консоль", "panelTitle"))
        local_description = label("Шоу редактируется и сохраняется локально. Потеря внешней связи не меняет текущий свет.", "muted")
        local_description.setWordWrap(True)
        content.addWidget(local_description)
        content.addStretch(1)
        layout.addWidget(frame)
        return page

    def _check_prop_presenter(self):
        host = self.pp_host.text().strip()
        port = self.pp_port.value()
        if not host or port == 0:
            self._set_pp_status("НУЖНЫ ДАННЫЕ", "Укажите адрес и порт из ProPresenter → Preferences → Network.", AMBER)
            return
        if getattr(self, "_pp_socket", None):
            self._pp_socket.abort()
        self._pp_socket = QTcpSocket(self)
        self._pp_socket.connected.connect(self._propresenter_port_connected)
        self._pp_socket.errorOccurred.connect(self._propresenter_port_failed)
        self._set_pp_status("ПРОВЕРКА", f"Проверяю {host}:{port}…", ACCENT)
        self.pp_probe_timer.start(2500)
        self._pp_socket.connectToHost(host, port)

    def _set_pp_status(self, badge, message, color):
        self.pp_badge.setText(badge)
        self.pp_badge.setStyleSheet(f"color: {color}; border-color: {color};")
        self.pp_status.setText(message)
        self.pp_status.setStyleSheet(f"color: {color};")

    def _propresenter_port_connected(self):
        self.pp_probe_timer.stop()
        self._set_pp_status("TCP ДОСТУПЕН", "Порт отвечает · API ещё не проверен", MINT)
        self._pp_socket.abort()

    def _propresenter_port_failed(self, error):
        if not self.pp_probe_timer.isActive():
            return
        self.pp_probe_timer.stop()
        error = self._pp_socket.error()
        if error == QAbstractSocket.SocketError.HostNotFoundError:
            message = "Компьютер с таким адресом не найден"
        elif error == QAbstractSocket.SocketError.ConnectionRefusedError:
            message = "Порт закрыт или ProPresenter не запущен"
        elif error == QAbstractSocket.SocketError.SocketAccessError:
            message = "Операционная система запретила сетевую проверку"
        else:
            message = f"Проверка не прошла · {self._pp_socket.errorString()}"
        self._set_pp_status("НЕТ СВЯЗИ", message, RED)

    def _propresenter_port_timeout(self):
        self.pp_probe_timer.stop()
        if self._pp_socket.state() != QTcpSocket.SocketState.ConnectedState:
            self._pp_socket.abort()
            self._set_pp_status("ТАЙМ-АУТ", "Нет ответа за 2,5 с · проверьте адрес, порт и Network", AMBER)

    def _stylesheet(self):
        return f"""
        QWidget#root {{ background: {BG}; color: {TEXT}; font-family: 'Segoe UI'; font-size: 10pt; }}
        QFrame#topbar {{ background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #1a222c, stop:1 {SURFACE}); border: 1px solid #34414e; border-radius: 16px; }}
        QFrame#sidebar, QFrame#panel {{ background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 #18212c, stop:0.48 {SURFACE}, stop:1 #10161e); border: 1px solid #34414e; border-radius: 16px; }}
        QFrame#miniCard {{ background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #202a36, stop:1 {SURFACE_2}); border: 1px solid #34414e; border-radius: 12px; }}
        QDialog {{ background: {SURFACE}; color: {TEXT}; }}
        QLabel[role='brand'] {{ color: {TEXT}; font-size: 19pt; font-weight: 800; letter-spacing: 3px; }}
        QLabel[role='eyebrow'] {{ color: {MUTED}; font-size: 8pt; font-weight: 700; letter-spacing: 1px; }}
        QLabel[role='showName'] {{ color: {TEXT}; font-size: 11pt; font-weight: 600; }}
        QLabel[role='panelTitle'] {{ color: {TEXT}; font-size: 11pt; font-weight: 650; }}
        QLabel[role='muted'] {{ color: {MUTED}; }}
        QLabel[role='emptyState'] {{ color: {MUTED}; background: {SURFACE_2}; border: 1px dashed {LINE}; border-radius: 9px; padding: 8px 12px; font-size: 9pt; }}
        QLabel[role='liveScene'] {{ color: {MINT}; font-size: 8pt; font-weight: 700; }}
        QLabel[role='previewScene'] {{ color: {ACCENT}; font-size: 8pt; font-weight: 700; }}
        QLabel[role='badge'] {{ color: {AMBER}; background: #29251d; border: 1px solid #49412e; border-radius: 10px; padding: 7px 10px; font-size: 8pt; font-weight: 700; }}
        QLabel[role='status'] {{ color: {MINT}; font-size: 8pt; font-weight: 650; }}
        QLabel[role='value'] {{ color: {TEXT}; font-size: 9pt; font-weight: 700; }}
        QLabel[role='selectedName'] {{ color: {ACCENT}; font-weight: 700; padding: 9px; background: {SURFACE_2}; border-radius: 9px; }}
        QLabel#statusBar {{ background: {SURFACE}; color: {MUTED}; border: 1px solid {LINE}; border-radius: 10px; padding: 7px 11px; }}
        QPushButton {{ color: {TEXT}; background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #222d39, stop:1 {SURFACE_2}); border: 1px solid #34414e; border-radius: 9px; padding: 9px 12px; }}
        QPushButton:hover {{ background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #2b3947, stop:1 {SURFACE_3}); border-color: #60778a; }}
        QPushButton:focus {{ border-color: {ACCENT}; }}
        QPushButton:checked {{ color: {ACCENT}; background: {ACCENT_DARK}; border-color: #3e6b79; }}
        QPushButton[role='primary'] {{ color: #101a20; background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #b4e9f2, stop:1 {ACCENT}); border-color: #b4e9f2; font-weight: 700; }}
        QPushButton[role='primary']:hover {{ background: #c5f0f6; }}
        QPushButton[role='danger'] {{ color: #fff0f1; background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #512a35, stop:1 #38202a); border-color: #85505e; font-weight: 700; }}
        QPushButton#blackoutButton {{ border: 3px solid #85505e; }}
        QPushButton#blackoutButton:checked {{ color: #ffffff; background: #a91f38; border: 3px solid #ff4c68; font-weight: 700; }}
        QPushButton#blackoutButton:checked[pulse='true'] {{ background: #d72848; border: 3px solid #ffdce2; }}
        QSplitter::handle:horizontal {{ background: #293541; width: 8px; margin: 2px; border-radius: 4px; }}
        QSplitter::handle:horizontal:hover {{ background: {ACCENT}; }}
        QPushButton:disabled {{ color: #687585; background: #171d26; border-color: #252f3a; }}
        QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QListWidget, QTableWidget {{ background: {SURFACE_2}; color: {TEXT}; border: 1px solid {LINE}; border-radius: 9px; padding: 7px; selection-background-color: {ACCENT_DARK}; }}
        QTabWidget::pane {{ background: {SURFACE_2}; border: 1px solid {LINE}; border-radius: 9px; top: -1px; }}
        QTabBar::tab {{ color: {MUTED}; background: {SURFACE_2}; border: 1px solid {LINE}; padding: 7px 11px; margin-right: 3px; border-top-left-radius: 7px; border-top-right-radius: 7px; }}
        QTabBar::tab:selected {{ color: {TEXT}; background: {ACCENT_DARK}; border-color: #3e6b79; }}
        QScrollArea {{ background: transparent; border: 0; }}
        QScrollArea QWidget#qt_scrollarea_viewport {{ background: transparent; }}
        QScrollBar:vertical {{ background: {SURFACE}; width: 8px; margin: 2px; border-radius: 4px; }}
        QScrollBar::handle:vertical {{ background: {SURFACE_3}; min-height: 24px; border-radius: 4px; }}
        QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ height: 0; }}
        QScrollBar:horizontal {{ background: {SURFACE}; height: 7px; margin: 2px; border-radius: 3px; }}
        QScrollBar::handle:horizontal {{ background: {SURFACE_3}; min-width: 28px; border-radius: 3px; }}
        QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {{ width: 0; }}
        QHeaderView::section {{ color: {MUTED}; background: {SURFACE_2}; border: 0; border-bottom: 1px solid {LINE}; padding: 9px; }}
        QListWidget::item {{ padding: 8px; border-radius: 7px; }}
        QListWidget::item:selected {{ background: {ACCENT_DARK}; color: {TEXT}; }}
        QSlider::groove:horizontal {{ height: 5px; background: {SURFACE_3}; border-radius: 2px; }}
        QSlider::handle:horizontal {{ width: 14px; margin: -5px 0; background: {ACCENT}; border: 2px solid #f3eaff; border-radius: 8px; }}
        QFrame#separator {{ color: {LINE}; }}
        QMenu {{ background: {SURFACE_2}; color: {TEXT}; border: 1px solid {LINE}; padding: 5px; }}
        QMenu::item:selected {{ background: {ACCENT_DARK}; }}
        """

    def _select_page(self, index):
        if not hasattr(self, "pages"):
            return
        self.pages.setCurrentIndex(index)
        for i, item in enumerate(self.nav_buttons):
            item.setChecked(i == index)
        if index in (0, 1, 2):
            self.refresh_stage_views()

    def keyPressEvent(self, event):
        """Run console shortcuts only after focused controls process their own keys."""
        key = event.key()
        modifiers = event.modifiers()
        command = bool(modifiers & (Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.MetaModifier))
        shift = bool(modifiers & Qt.KeyboardModifier.ShiftModifier)
        if command:
            actions = {
                Qt.Key.Key_S: self._save_dialog,
                Qt.Key.Key_O: self._open_dialog,
                Qt.Key.Key_N: self._new_show,
                Qt.Key.Key_D: self._duplicate_selection,
            }
            if key == Qt.Key.Key_Z:
                (self.redo if shift else self.undo)()
            elif key == Qt.Key.Key_Y:
                self.redo()
            elif key == Qt.Key.Key_C:
                self._copy_selection()
            elif key == Qt.Key.Key_X:
                self._copy_selection(cut=True)
            elif key == Qt.Key.Key_V:
                self._paste_current()
            elif key in actions:
                actions[key]()
            else:
                super().keyPressEvent(event)
                return
            event.accept()
            return
        if key == Qt.Key.Key_Delete:
            self._delete_current_selection()
            event.accept()
        elif key == Qt.Key.Key_F2:
            self._configure_selection()
            event.accept()
        else:
            super().keyPressEvent(event)

    def _refresh_ports(self):
        previous = self.port_combo.currentText()
        self.port_combo.clear()
        self.port_combo.addItems(DmxOutput.available_ports())
        self.port_combo.setCurrentText(previous)

    def _toggle_dmx(self):
        try:
            if self.output.connected:
                self.output.disconnect()
                self.dmx_button.setText("Подключить")
                self.connection_badge.setText("●  DMX ОТКЛЮЧЁН")
                self.status_bar.setText("DMX отключён · шоу продолжает работать локально")
            else:
                port = self.port_combo.currentText().strip()
                if not port:
                    raise ValueError("Выберите COM-порт для подключения.")
                self.output.connect(port)
                self.dmx_button.setText("Отключить")
                self.connection_badge.setText(f"●  {port} · DMX")
                self._send_dmx()
                self.status_bar.setText(f"DMX подключён · {port}")
        except Exception as exc:
            QMessageBox.warning(self, "Подключение DMX", str(exc))

    def _refresh_dmx(self):
        self._send_dmx()
        if self.output.connected:
            self.status_bar.setText("DMX обновлён · текущие значения отправлены")
        else:
            self.status_bar.setText("DMX не подключён · значения света остаются в шоу")

    def _handle_dmx_write_failure(self, error, generation):
        if generation != self.output.generation:
            return
        self.output.disconnect()
        self.dmx_button.setText("Подключить")
        self.connection_badge.setText("●  DMX ОШИБКА")
        self.status_bar.setText(f"Ошибка DMX · {error}")
        QMessageBox.warning(self, "Ошибка DMX-выхода", f"Передача DMX остановлена. Проверьте кабель и интерфейс.\n\n{error}")

    def _toggle_blackout(self):
        self.blackout_active = not self.blackout_active
        self.blackout_button.setChecked(self.blackout_active)
        if self.blackout_active:
            self._blackout_pulse = False
            self.blackout_button.setProperty("pulse", "false")
            self.blackout_timer.start()
        else:
            self.blackout_timer.stop()
            self.blackout_button.setProperty("pulse", "false")
        self.blackout_button.style().unpolish(self.blackout_button)
        self.blackout_button.style().polish(self.blackout_button)
        self.blackout_button.update()
        self._send_dmx(); self.refresh_stage_views()
        self.status_bar.setText("BLACKOUT · все каналы затемнены" if self.blackout_active else "Текущий свет восстановлен")

    def _pulse_blackout_edge(self):
        if not self.blackout_active:
            self.blackout_timer.stop()
            return
        self._blackout_pulse = not self._blackout_pulse
        self.blackout_button.setProperty("pulse", "true" if self._blackout_pulse else "false")
        self.blackout_button.style().unpolish(self.blackout_button)
        self.blackout_button.style().polish(self.blackout_button)
        self.blackout_button.update()

    def _set_channel(self, key, value):
        if not hasattr(self, "show_data"):
            return
        if self._fade:
            self._cancel_fade()
        selected_ids = set(self.selected_fixture_ids)
        targets = [f for f in self.show_data["fixtures"] if f["id"] in selected_ids]
        previous = self.gang_fader_previous.get(key, value)
        delta = value - previous
        self.gang_fader_previous[key] = value
        if not targets or not delta:
            self.control_titles[key].setText(str(value))
            return
        linked = next((gang for gang in self.show_data.get("gangs", [])
                       if key in gang.get("scope", []) and selected_ids
                       and selected_ids.issubset(set(gang.get("members", [])))), None)
        if linked and not selected_ids.intersection(self.gang_isolated_ids):
            targets = [f for f in self.show_data["fixtures"]
                       if f["id"] in linked.get("members", []) and f["id"] not in self.gang_isolated_ids]
        for fixture in targets:
            look = fixture.setdefault("look", blank_look())
            look[key] = max(0, min(255, int(look.get(key, 0)) + delta))
        for fixture in targets:
            mirror_id = fixture.get("mirror_group_id")
            if mirror_id:
                new_value = fixture["look"][key]
                for mirror in self.show_data["fixtures"]:
                    if mirror.get("mirror_group_id") == mirror_id:
                        mirror.setdefault("look", blank_look())[key] = new_value
        if targets:
            self.dirty = True
            self.control_titles[key].setText(str(value))
            self._update_color_swatch()
            self.refresh_stage_views()
            self._send_dmx()

    def _send_dmx(self):
        values = [0] * 512
        for fixture in ([] if self.blackout_active else self.show_data.get("fixtures", [])):
            address = fixture["address"] - 1
            dimmer = max(0, min(255, int(fixture.get("look", {}).get("dimmer", 255))))
            for channel in ("r", "g", "b", "w"):
                slot = address + fixture["offsets"].get(channel, 0)
                if 0 <= slot < 512:
                    raw = max(0, min(255, int(fixture.get("look", {}).get(channel, 0))))
                    values[slot] = round(raw * dimmer / 255)
        if self.output.connected:
            self.output.send_frame(bytes(values))

    def _fixture_selection(self):
        if not hasattr(self, "fixture_list"):
            return
        self.selected_fixture_ids = {item.data(Qt.ItemDataRole.UserRole) for item in self.fixture_list.selectedItems()}
        fixtures = [f for f in self.show_data["fixtures"] if f["id"] in self.selected_fixture_ids]
        self.selected_name.setText(", ".join(f["name"] for f in fixtures) or "Нет выбора")
        self._sync_programmer_controls(fixtures)
        self._sync_patch_selection()
        self._sync_stage_fixture_focus()
        self._update_color_swatch()

    def _patch_selection(self):
        if getattr(self, "_patch_sync", False): return
        rows = {index.row() for index in self.patch_table.selectionModel().selectedRows()}
        self.selected_fixture_ids = {self.show_data["fixtures"][row]["id"] for row in rows if row < len(self.show_data["fixtures"])}
        self._fixture_selection_from_ids()

    def _sync_programmer_controls(self, fixtures):
        enabled = bool(fixtures)
        for key, slider in self.faders.items():
            slider.setEnabled(enabled)
            if enabled:
                value = round(sum(f.get("look", {}).get(key, 0) for f in fixtures) / len(fixtures))
                slider.blockSignals(True); slider.setValue(value); slider.blockSignals(False)
                self.control_titles[key].setText(str(value))
            else:
                slider.blockSignals(True); slider.setValue(0); slider.blockSignals(False)
                self.control_titles[key].setText("—")
            self.gang_fader_previous[key] = slider.value()
        self.color_wheel.setEnabled(enabled)
        self.save_color_button.setEnabled(enabled)
        self.color_palette_scroll.setEnabled(enabled)

    def _sync_patch_selection(self):
        if not hasattr(self, "patch_table"):
            return
        self._patch_sync = True
        self.patch_table.clearSelection()
        for row, fixture in enumerate(self.show_data.get("fixtures", [])):
            if row < self.patch_table.rowCount() and fixture["id"] in self.selected_fixture_ids:
                self.patch_table.selectRow(row)
        self._patch_sync = False

    def _fixture_selection_from_ids(self):
        fixtures = [f for f in self.show_data["fixtures"] if f["id"] in self.selected_fixture_ids]
        self.selected_name.setText(", ".join(f["name"] for f in fixtures) or "Нет выбора")
        self._sync_programmer_controls(fixtures)
        self._sync_patch_selection()
        self._sync_stage_fixture_focus()
        self._update_color_swatch()

    def _sync_stage_fixture_focus(self):
        selected = set(self.selected_fixture_ids)
        if len(selected) == 1:
            fixture_id = next(iter(selected))
            stage_object = next((obj for obj in self.show_data.get("stage", {}).get("objects", [])
                                 if obj.get("kind") == "fixture" and obj.get("fixture_id") == fixture_id), None)
            if stage_object: self.selected_stage_id = stage_object.get("id")
        elif selected:
            self.selected_stage_id = None
        else:
            current = self._selected_stage_object()
            if current and current.get("kind") == "fixture": self.selected_stage_id = None
        for view_name in ("live_stage", "editor_stage", "cue_live_stage", "cue_stage"):
            view = getattr(self, view_name, None)
            if view: view.set_selected(self.selected_stage_id)
        if hasattr(self, "stage_name"):
            self._sync_stage_inspector()

    def _fixture_context_menu(self, pos):
        item = self.fixture_list.itemAt(pos)
        if item and not item.isSelected():
            self.fixture_list.clearSelection(); item.setSelected(True)
        menu = QMenu(self)
        configure = menu.addAction("Настроить прибор в патче")
        copy_action = menu.addAction("Копировать")
        cut_action = menu.addAction("Вырезать")
        paste_action = menu.addAction("Вставить")
        paste_action.setEnabled(getattr(self, "_clipboard", (None,))[0] == "fixture")
        delete = menu.addAction("Удалить")
        selected = menu.exec(self.fixture_list.mapToGlobal(pos))
        if selected == configure:
            self._select_page(3)
        elif selected == copy_action:
            self._copy_selection()
        elif selected == cut_action:
            self._copy_selection(cut=True)
        elif selected == paste_action:
            self._paste_current()
        elif selected == delete:
            self._delete_fixtures()

    def _cue_context_menu(self, pos):
        item = self.cue_list.itemAt(pos)
        if item: self.cue_list.setCurrentItem(item)
        menu = QMenu(self)
        configure = menu.addAction("Настроить")
        copy_action = menu.addAction("Копировать")
        cut_action = menu.addAction("Вырезать")
        paste_action = menu.addAction("Вставить")
        paste_action.setEnabled(getattr(self, "_clipboard", (None,))[0] == "cue")
        delete = menu.addAction("Удалить")
        selected = menu.exec(self.cue_list.mapToGlobal(pos))
        if selected == configure: self._edit_cue()
        elif selected == copy_action: self._copy_selection()
        elif selected == cut_action: self._copy_selection(cut=True)
        elif selected == paste_action: self._paste_current()
        elif selected == delete: self._delete_cue()

    def _copy_selection(self, cut=False):
        focus = self.focusWidget()
        stage_focus = focus in (self.live_stage, self.editor_stage)
        if self.pages.currentIndex() == 1 or stage_focus:
            obj = self._selected_stage_object()
            if obj:
                self._clipboard = ("stage", copy.deepcopy(obj))
                if cut: self._delete_stage()
        elif self.pages.currentIndex() == 2:
            cue = self._selected_cue()
            if cue:
                self._clipboard = ("cue", copy.deepcopy(cue))
                if cut: self._delete_cue()
        elif self.pages.currentIndex() in (0, 3):
            fixtures = [copy.deepcopy(f) for f in self.show_data["fixtures"] if f["id"] in self.selected_fixture_ids]
            if fixtures:
                self._clipboard = ("fixture", fixtures)
                if cut: self._delete_fixtures()

    def _paste_current(self):
        clipboard = getattr(self, "_clipboard", None)
        if not clipboard: return
        kind, source = clipboard
        page = self.pages.currentIndex()
        if kind == "stage" and page in (0, 1):
            self._stage_action({"duplicate": source})
        elif kind == "cue" and page == 2:
            self._checkpoint()
            cue = copy.deepcopy(source); cue["id"] = new_id(); cue["label"] = cue.get("label", "Snapshot") + " — копия"
            original = next((s for s in self.show_data["scenes"] if s["id"] == source.get("scene_id")), None)
            scene = copy.deepcopy(original or {"name": cue["label"], "look": cue.get("look", {})})
            scene["id"] = new_id(); scene["name"] = cue["label"]; cue["scene_id"] = scene["id"]
            self.show_data["scenes"].append(scene); self.show_data["cues"].append(cue)
            self.preview_cue_id = cue["id"]; self.dirty = True; self.refresh_all()
        elif kind == "fixture" and page in (0, 3):
            self._checkpoint()
            occupied = {f["address"] + offset for f in self.show_data["fixtures"] for offset in f.get("offsets", {}).values()}
            inserted = set()
            for original in source:
                fixture = copy.deepcopy(original); fixture["id"] = new_id(); fixture.pop("mirror_group_id", None)
                fixture["name"] = fixture.get("name", "PAR") + " — копия"
                offsets = fixture.get("offsets", {"r": 0, "g": 1, "b": 2, "w": 3})
                address = next((n for n in range(1, 513) if n + max(offsets.values()) <= 512 and
                                all(n + offset not in occupied and n + offset not in inserted for offset in offsets.values())), None)
                if address is None: break
                fixture["address"] = address; inserted.update(address + offset for offset in offsets.values())
                self.show_data["fixtures"].append(fixture); self.selected_fixture_ids.add(fixture["id"])
            self.dirty = True; self.refresh_all()

    def _duplicate_selection(self):
        self._copy_selection()
        self._paste_current()

    def _delete_current_selection(self):
        if self.pages.currentIndex() == 1: self._delete_stage()
        elif self.pages.currentIndex() == 2: self._delete_cue()
        elif self.pages.currentIndex() in (0, 3): self._delete_fixtures()

    def _configure_selection(self):
        if self.pages.currentIndex() == 1 or self.focusWidget() in (self.live_stage, self.editor_stage):
            self._select_page(1)
            self._sync_stage_inspector()
        elif self.pages.currentIndex() == 2:
            self._edit_cue()
        elif self.pages.currentIndex() == 3:
            self._select_page(3)

    def closeEvent(self, event):
        if not self._confirm_unsaved():
            event.ignore()
            return
        self._cancel_fade()
        self.output.disconnect()
        event.accept()

    def _add_fixture(self):
        used = {f["address"] + offset for f in self.show_data["fixtures"] for offset in f.get("offsets", {}).values()}
        address = next((n for n in range(1, 510) if all(n + offset not in used for offset in (0, 1, 2, 3))), None)
        if address is None:
            QMessageBox.warning(self, "Патч", "В универсуме больше нет свободных каналов.")
            return
        fixture = {"id": new_id(), "name": f"PAR {len(self.show_data['fixtures']) + 1:02d}", "address": address,
                   "group": "Сцена", "offsets": {"r": 0, "g": 1, "b": 2, "w": 3}, "look": blank_look()}
        self._checkpoint(); self.show_data["fixtures"].append(fixture); self.dirty = True; self.refresh_all()

    def _delete_fixtures(self):
        return self._remove_fixtures(self.selected_fixture_ids)

    def _remove_fixtures(self, fixture_ids, checkpoint=True, refresh=True):
        ids = set(fixture_ids)
        if not ids:
            return
        if checkpoint:
            self._checkpoint()
        self.show_data["fixtures"] = [f for f in self.show_data["fixtures"] if f["id"] not in ids]
        self.gang_isolated_ids.difference_update(ids)
        for gang in self.show_data.get("gangs", []):
            gang["members"] = [fid for fid in gang.get("members", []) if fid not in ids]
        self.show_data["gangs"] = [gang for gang in self.show_data.get("gangs", []) if len(gang.get("members", [])) >= 2]
        stage = self.show_data["stage"]
        removed_stage_ids = {o.get("id") for objects in [stage.get("objects", []),
                             *(layout.get("objects", []) for layout in stage.get("layouts", []) if isinstance(layout, dict))]
                             for o in objects if isinstance(o, dict) and o.get("fixture_id") in ids}
        stage["objects"] = [o for o in stage.get("objects", []) if o.get("fixture_id") not in ids]
        for layout in stage.get("layouts", []):
            if isinstance(layout, dict):
                layout["objects"] = [o for o in layout.get("objects", []) if o.get("fixture_id") not in ids]
        if self.selected_stage_id in removed_stage_ids:
            self.selected_stage_id = None
        for scene in self.show_data.get("scenes", []):
            for fixture_id in ids: scene.get("look", {}).pop(fixture_id, None)
        for cue in self.show_data.get("cues", []):
            for fixture_id in ids:
                cue.get("look", {}).pop(fixture_id, None)
            cue["update_fixtures"] = [fixture_id for fixture_id in cue.get("update_fixtures", []) if fixture_id not in ids]
        self.selected_fixture_ids.difference_update(ids); self.dirty = True
        if refresh:
            self.refresh_all()

    def _patch_item_changed(self, item):
        if getattr(self, "_patch_sync", False) or item.column() not in (0, 1, 2): return
        row = item.row()
        if not 0 <= row < len(self.show_data["fixtures"]): return
        candidate = copy.deepcopy(self.show_data)
        fixture = candidate["fixtures"][row]
        try:
            if item.column() == 0:
                name = item.text().strip()
                if not name: raise ValueError("Название прибора не может быть пустым.")
                fixture["name"] = name
            elif item.column() == 1:
                fixture["address"] = int(item.text())
            else:
                group = item.text().strip()
                if not group: raise ValueError("Название группы не может быть пустым.")
                fixture["group"] = group
                if group not in candidate["groups"]: candidate["groups"].append(group)
            ShowSchema.validate(candidate)
            self._checkpoint(); self.show_data = candidate; self.dirty = True
        except Exception as exc:
            QMessageBox.warning(self, "Патч", str(exc))
        self.refresh_all()

    def _stage_action(self, action=None):
        if isinstance(action, dict):
            if "begin_transform" in action:
                self._checkpoint()
                return
            if "geometry_commit" in action:
                self._sync_symmetric_pair(action.get("object_id"))
                self.dirty = True
                self.show_name.setText(self.show_data["name"] + "  •")
                self.refresh_stage_views()
                self._sync_stage_inspector()
                return
            if "add" in action:
                self._checkpoint()
                kind = action["add"]
                instrument = action.get("instrument") or "guitar"
                if kind == "musician" and ("x" not in action or "y" not in action):
                    count = sum(item.get("kind") == "musician" for item in self.show_data["stage"].get("objects", []))
                    x = .16 + (count % 4) * .22
                    y = .43 + (count // 4) * .27
                else:
                    x, y = action.get("x", .42), action.get("y", .42)
                musician_names = {"vocal": "Вокал", "guitar": "Гитара", "bass": "Бас", "keys": "Клавиши", "drums": "Ударные"}
                obj = {"id": new_id(), "kind": kind, "label": musician_names.get(instrument, "Музыкант") if kind == "musician" else {"label": "Ориентир", "rect": "Область", "circle": "Зона", "column": "Колонна"}.get(kind, "Ориентир"),
                       "x": x, "y": y, "w": .14 if kind == "musician" else .12,
                       "h": .22 if kind == "musician" else .13, "color": ACCENT}
                if kind == "musician": obj["instrument"] = instrument
                self.show_data["stage"].setdefault("objects", []).append(obj)
                if self.stage_symmetry.isChecked() and kind != "fixture":
                    twin = copy.deepcopy(obj); twin["id"] = new_id()
                    twin["symmetry_pair_id"] = obj["id"]
                    obj["symmetry_pair_id"] = twin["id"]
                    twin["x"] = 1.0 - float(obj["x"]) - float(obj["w"])
                    self.show_data["stage"]["objects"].append(twin)
                self.selected_stage_id = obj["id"]
                self.dirty = True
            elif "duplicate" in action:
                self._checkpoint(); obj = copy.deepcopy(action["duplicate"]); obj["id"] = new_id()
                obj["x"], obj["y"] = min(.9, obj.get("x", .5) + .04), min(.87, obj.get("y", .5) + .04)
                self.show_data["stage"].setdefault("objects", []).append(obj); self.selected_stage_id = obj["id"]; self.dirty = True
            elif "copy" in action:
                self._clipboard = ("stage", copy.deepcopy(action["copy"]))
            elif "cut" in action:
                self._clipboard = ("stage", copy.deepcopy(action["cut"]))
                self.selected_stage_id = action["cut"].get("id")
                self._delete_stage()
                return
            elif "paste" in action:
                self._paste_current()
                return
            elif "delete" in action:
                self.selected_stage_id = action["delete"]; self._delete_stage({action["delete"]})
            elif action == "edit":
                self._select_page(1)
                self._sync_stage_inspector()
                return
        elif action == "edit":
            self._select_page(1)
            self._sync_stage_inspector()
            return
        self.refresh_stage_views(); self._sync_stage_inspector()

    def _set_stage_dimensions(self):
        if not hasattr(self, "stage_width"):
            return
        self.show_data["stage"]["width_m"] = self.stage_width.value()
        self.show_data["stage"]["depth_m"] = self.stage_depth.value()

    def _ensure_stage_layouts(self):
        stage = self.show_data.setdefault("stage", {"width_m": 8, "depth_m": 6, "objects": []})
        layouts = stage.setdefault("layouts", [])
        if not layouts:
            layout_id = new_id()
            layouts.append({"id": layout_id, "name": "Основная сцена", "objects": copy.deepcopy(stage.get("objects", []))})
            stage["active_layout_id"] = layout_id
        active = next((layout for layout in layouts if layout.get("id") == stage.get("active_layout_id")), None)
        if active is None:
            active = layouts[0]
            stage["active_layout_id"] = active["id"]
        active["objects"] = copy.deepcopy(stage.get("objects", []))
        if hasattr(self, "stage_layout_picker"):
            old = self.stage_layout_picker.blockSignals(True)
            self.stage_layout_picker.clear()
            for entry in layouts:
                self.stage_layout_picker.addItem(entry.get("name", "Сцена"), entry.get("id"))
            self.stage_layout_picker.setCurrentIndex(max(0, self.stage_layout_picker.findData(active["id"])))
            self.stage_layout_picker.blockSignals(old)
            if hasattr(self, "delete_stage_layout_button"):
                self.delete_stage_layout_button.setEnabled(len(layouts) > 1)

    def _stage_layout_selected(self, index):
        if index < 0 or not self.show_data.get("stage", {}).get("layouts"):
            return
        layout_id = self.stage_layout_picker.itemData(index)
        if layout_id and layout_id != self.show_data["stage"].get("active_layout_id"):
            self._activate_stage_layout(layout_id)

    def _activate_stage_layout(self, layout_id, mark_dirty=True):
        stage = self.show_data["stage"]
        if mark_dirty:
            self._checkpoint()
        current = next((entry for entry in stage.get("layouts", []) if entry.get("id") == stage.get("active_layout_id")), None)
        if current:
            current["objects"] = copy.deepcopy(stage.get("objects", []))
        target = next((entry for entry in stage.get("layouts", []) if entry.get("id") == layout_id), None)
        if not target:
            return
        stage["active_layout_id"] = layout_id
        stage["objects"] = copy.deepcopy(target.get("objects", []))
        self._ensure_stage_fixtures()
        if mark_dirty:
            self.dirty = True
        self.refresh_all()

    def _save_stage_layout_as(self):
        name, accepted = self._ask_text("Сохранить план сцены", "Название состава / плана:",
                                        f"Сцена {len(self.show_data['stage'].get('layouts', [])) + 1}")
        if not accepted or not name:
            return
        self._checkpoint()
        stage = self.show_data["stage"]
        self._ensure_stage_layouts()
        layout_id = new_id()
        stage["layouts"].append({"id": layout_id, "name": name, "objects": copy.deepcopy(stage["objects"])})
        stage["active_layout_id"] = layout_id
        self.dirty = True; self.refresh_all()

    def _delete_stage_layout(self):
        stage = self.show_data["stage"]
        layouts = stage.get("layouts", [])
        if len(layouts) <= 1:
            return
        active_id = stage.get("active_layout_id")
        current = next((entry for entry in layouts if entry.get("id") == active_id), None)
        name = current.get("name", "план") if current else "план"
        answer = QMessageBox.question(self, "Удалить план сцены", f"Удалить сохранённый план «{name}»?",
                                      QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                      QMessageBox.StandardButton.No)
        if answer != QMessageBox.StandardButton.Yes:
            return
        self._checkpoint()
        stage["layouts"] = [entry for entry in layouts if entry.get("id") != active_id]
        target = stage["layouts"][0]
        for cue in self.show_data.get("cues", []):
            if cue.get("stage_layout_id") == active_id:
                cue["stage_layout_id"] = target["id"]
        stage["active_layout_id"] = target["id"]
        stage["objects"] = copy.deepcopy(target.get("objects", []))
        self._ensure_stage_fixtures()
        self.dirty = True; self.refresh_all()

    def _sync_symmetric_pair(self, object_id):
        if not self.stage_symmetry.isChecked() or not object_id:
            return
        objects = self.show_data["stage"].get("objects", [])
        source = next((item for item in objects if item.get("id") == object_id), None)
        if not source or not source.get("symmetry_pair_id"):
            return
        twin = next((item for item in objects if item.get("id") == source.get("symmetry_pair_id")), None)
        if twin:
            twin["x"] = 1.0 - float(source.get("x", .5)) - float(source.get("w", .12))
            twin["y"] = float(source.get("y", .5))
            twin["w"] = float(source.get("w", .12)); twin["h"] = float(source.get("h", .12))
            twin["rotation"] = -float(source.get("rotation", 0))
        self.dirty = True; self.refresh_stage_views()

    def _selected_stage_object(self):
        return next((o for o in self.show_data["stage"].get("objects", []) if o.get("id") == self.selected_stage_id), None)

    def _apply_stage_inspector(self, *_):
        obj = self._selected_stage_object()
        if not obj:
            return
        obj["label"] = self.stage_name.text().strip() or obj.get("label", "Объект")
        rgb = [self.stage_color_sliders[key].value() for key in ("r", "g", "b")]
        obj["color"] = QColor(*rgb).name()
        obj["w"], obj["h"] = self.object_width.value(), self.object_height.value()
        obj["rotation"] = self.object_rotation.value()
        if obj.get("kind") == "fixture":
            obj["beam_size"] = self.beam_size.value()
            obj["beam_length"] = self.beam_length.value()
        self.dirty = True; self.refresh_stage_views()

    def _apply_stage_diagonal(self, value):
        obj = self._selected_stage_object()
        if not obj:
            return
        ratio = max(.1, self.object_width.value() / max(.001, self.object_height.value()))
        height = min(.5, max(.05, value / math.sqrt(ratio * ratio + 1)))
        width = min(.5, max(.05, height * ratio))
        for widget, new_value in ((self.object_width, width), (self.object_height, height)):
            widget.blockSignals(True); widget.setValue(new_value); widget.blockSignals(False)
        self._apply_stage_inspector()

    def _sync_stage_inspector(self):
        obj = self._selected_stage_object()
        if hasattr(self, "delete_stage_button"):
            selected_count = len(self.editor_stage.stage.selectedItems()) if hasattr(self, "editor_stage") else 0
            if selected_count > 1:
                self.delete_stage_button.setText("Удалить выбранные")
            elif obj and obj.get("kind") == "fixture":
                self.delete_stage_button.setText("Удалить прибор")
            else:
                self.delete_stage_button.setText("Удалить объект")
            self.delete_stage_button.setEnabled(bool(obj) or selected_count > 1)
        all_widgets = (self.stage_name, self.object_width, self.object_height, self.object_diagonal,
                       self.object_rotation, self.beam_size, self.beam_length, *self.stage_color_sliders.values())
        for widget in all_widgets: widget.blockSignals(True)
        if obj:
            self.stage_name.setText(obj.get("label", ""))
            color = QColor(obj.get("color", ACCENT))
            for index, key in enumerate(("r", "g", "b")):
                channel_value = color.getRgb()[:3][index]
                self.stage_color_sliders[key].setValue(channel_value)
                self.stage_color_values[key].setText(str(channel_value))
            self.object_width.setValue(obj.get("w", .12)); self.object_height.setValue(obj.get("h", .15))
            self.object_diagonal.setValue(math.hypot(obj.get("w", .12), obj.get("h", .15)))
            self.object_rotation.setValue(obj.get("rotation", 0))
            self.beam_size.setValue(obj.get("beam_size", .8)); self.beam_length.setValue(obj.get("beam_length", 2.2))
        else:
            self.stage_name.clear()
            for key, slider in self.stage_color_sliders.items():
                slider.setValue(0); self.stage_color_values[key].setText("0")
            self.object_width.setValue(.12); self.object_height.setValue(.15)
            self.object_diagonal.setValue(math.hypot(.12, .15)); self.object_rotation.setValue(0)
            self.beam_size.setValue(.8); self.beam_length.setValue(2.2)
        self.beam_size.setEnabled(bool(obj and obj.get("kind") == "fixture"))
        self.beam_length.setEnabled(bool(obj and obj.get("kind") == "fixture"))
        for widget in all_widgets: widget.blockSignals(False)

    def _delete_stage(self, object_ids=None):
        if not isinstance(object_ids, (set, list, tuple)):
            object_ids = {item.data.get("id") for item in self.editor_stage.stage.selectedItems()
                          if isinstance(item, StageObject)}
            if not object_ids and self.selected_stage_id:
                object_ids = {self.selected_stage_id}
        else:
            object_ids = set(object_ids)
        objects = self.show_data["stage"].get("objects", [])
        selected_objects = [obj for obj in objects if obj.get("id") in object_ids]
        if not selected_objects:
            return
        fixture_ids = {obj.get("fixture_id") for obj in selected_objects if obj.get("kind") == "fixture"}
        self._checkpoint()
        self.show_data["stage"]["objects"] = [obj for obj in objects
                                                if obj.get("id") not in object_ids and
                                                not (obj.get("kind") == "fixture" and obj.get("fixture_id") in fixture_ids)]
        self.selected_stage_id = None
        self.dirty = True
        if fixture_ids:
            self._remove_fixtures(fixture_ids, checkpoint=False, refresh=False)
            self.refresh_all()
        else:
            self.refresh_stage_views()
            self._sync_stage_inspector()

    def _add_cue(self):
        label_text, ok = self._ask_text(
            "Новый snapshot",
            "Сохранит текущие уровни света всех приборов и активный план сцены.\n"
            "Переход по умолчанию: 1 с.\nНазвание:",
            f"Snapshot {len(self.show_data['cues']) + 1}",
        )
        if not ok: return
        self._checkpoint()
        look = {f["id"]: copy.deepcopy(f.get("look", blank_look())) for f in self.show_data["fixtures"]}
        scene = {"id": new_id(), "name": label_text, "look": copy.deepcopy(look)}
        cue = {"id": new_id(), "scene_id": scene["id"], "label": label_text, "fade": 1.0, "look": look,
               "stage_layout_id": self.show_data["stage"].get("active_layout_id"),
               "update_method": "manual", "update_channels": ["dimmer", "r", "g", "b", "w"],
               "update_fixtures": [f["id"] for f in self.show_data["fixtures"]], "update_group": []}
        self.show_data["scenes"].append(scene); self.show_data["cues"].append(cue)
        self.preview_cue_id = cue["id"]
        self.dirty = True; self.refresh_all()

    def _ask_text(self, title, prompt, initial=""):
        dialog = QDialog(self); dialog.setWindowTitle(title)
        box = QVBoxLayout(dialog)
        prompt_label = label(prompt)
        prompt_label.setWordWrap(True)
        box.addWidget(prompt_label)
        editor = QLineEdit(initial); box.addWidget(editor)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(dialog.accept); buttons.rejected.connect(dialog.reject); box.addWidget(buttons)
        accepted = dialog.exec() == QDialog.DialogCode.Accepted
        return editor.text().strip(), accepted

    def _cue_preview_item(self, item):
        self.preview_cue_id = item.data(Qt.ItemDataRole.UserRole)
        self.refresh_stage_views()
        self._update_cue_preview_label()

    def _cue_selection(self, current, _previous):
        if current:
            self.preview_cue_id = current.data(Qt.ItemDataRole.UserRole)
            self.refresh_stage_views()
            self._update_cue_preview_label()

    def _update_cue_preview_label(self):
        cue = next((entry for entry in self.show_data.get("cues", [])
                    if entry.get("id") == self.preview_cue_id), None)
        live_cue = next((entry for entry in self.show_data.get("cues", [])
                         if entry.get("id") == self.live_cue_id), None)
        if live_cue:
            live_number = self._cue_number_for(live_cue)
            live_scene = self._scene_number_for_cue(live_cue)
            self.cue_live_scene_caption.setText(f"● LIVE · SNAPSHOT {live_number:02d} · СЦЕНА {live_scene:02d} · {live_cue.get('label', '')}")
        else:
            self.cue_live_scene_caption.setText("● LIVE · НЕТ ВЫЗВАННОГО SNAPSHOT")
        if cue is None:
            self.cue_preview_info.setText("Выберите snapshot для предпросмотра")
            self.cue_preview_info.setStyleSheet(f"color: {MUTED};")
            self.cue_preview_scene_caption.setText("◉ ПРЕДПРОСМОТР · НЕ ВЫБРАН")
            return
        live = cue.get("id") == self.live_cue_id
        state = "В ЭФИРЕ" if live else "ПРЕДПРОСМОТР"
        color = MINT if live else ACCENT
        cue_number = self._cue_number_for(cue)
        scene_number = self._scene_number_for_cue(cue)
        self.cue_preview_info.setText(f"{state} · SNAPSHOT {cue_number:02d} · СЦЕНА {scene_number:02d} · {cue.get('label', 'Snapshot')} · переход {float(cue.get('fade', 0)):g} с")
        self.cue_preview_info.setStyleSheet(f"color: {color}; font-weight: 700;")
        self.cue_preview_scene_caption.setText(f"◉ ПРЕДПРОСМОТР · SNAPSHOT {cue_number:02d} · СЦЕНА {scene_number:02d} · {cue.get('label', 'Snapshot')}")

    def _cue_number_for(self, cue):
        return next((index for index, entry in enumerate(self.show_data.get("cues", []), start=1)
                     if entry.get("id") == cue.get("id")), 0)

    def _scene_number_for_cue(self, cue):
        return next((index for index, entry in enumerate(self.show_data.get("scenes", []), start=1)
                     if entry.get("id") == cue.get("scene_id")), 0)

    def _edit_cue(self):
        cue = self._selected_cue()
        if not cue: return
        dialog = QDialog(self); dialog.setWindowTitle(f"Настроить snapshot · {cue.get('label', 'Snapshot')}")
        dialog.resize(850, min(760, 250 + len(self.show_data["fixtures"]) * 44))
        box = QVBoxLayout(dialog)
        top = QHBoxLayout()
        name_box = QVBoxLayout(); name_box.addWidget(label("Название"))
        name = QLineEdit(cue.get("label", "Snapshot")); name_box.addWidget(name)
        top.addLayout(name_box, 1)
        fade_box = QVBoxLayout(); fade_box.addWidget(label("ПЕРЕХОД" , "eyebrow"))
        fade = QDoubleSpinBox(); fade.setRange(0, 600); fade.setDecimals(2); fade.setSingleStep(.25); fade.setSuffix(" с")
        fade.setValue(float(cue.get("fade", 0))); fade_box.addWidget(fade)
        top.addLayout(fade_box)
        box.addLayout(top)
        layout_row = QHBoxLayout()
        layout_row.addWidget(label("План сцены"))
        layout_picker = QComboBox()
        for entry in self.show_data.get("stage", {}).get("layouts", []):
            layout_picker.addItem(entry.get("name", "Сцена"), entry.get("id"))
        selected_layout = cue.get("stage_layout_id", self.show_data["stage"].get("active_layout_id"))
        layout_picker.setCurrentIndex(max(0, layout_picker.findData(selected_layout)))
        layout_row.addWidget(layout_picker, 1)
        box.addLayout(layout_row)
        box.addWidget(label("УРОВНИ ПРИБОРОВ", "eyebrow"))
        box.addWidget(label("Отредактируйте сохранённый свет или заполните значения из текущего LIVE.", "muted"))
        table = QTableWidget(len(self.show_data["fixtures"]), 6)
        table.setHorizontalHeaderLabels(["Прибор", "Яркость", "Красный", "Зелёный", "Синий", "Белый"])
        table.verticalHeader().setVisible(False)
        table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        table.setSelectionMode(QTableWidget.SelectionMode.NoSelection)
        table.horizontalHeader().setStretchLastSection(True)
        table.setColumnWidth(0, 170)
        keys = ("dimmer", "r", "g", "b", "w")
        cue_look = cue.get("look", {})
        spinboxes = {}
        for row, fixture in enumerate(self.show_data["fixtures"]):
            item = QTableWidgetItem(fixture.get("name", "Прибор"))
            item.setData(Qt.ItemDataRole.UserRole, fixture["id"])
            table.setItem(row, 0, item)
            look = cue_look.get(fixture["id"], fixture.get("look", blank_look()))
            for col, key in enumerate(keys, start=1):
                spinner = QSpinBox(); spinner.setRange(0, 255); spinner.setButtonSymbols(QSpinBox.ButtonSymbols.NoButtons)
                spinner.setValue(max(0, min(255, int(look.get(key, 0))))); spinner.setAlignment(Qt.AlignmentFlag.AlignCenter)
                table.setCellWidget(row, col, spinner); spinboxes[(fixture["id"], key)] = spinner
        box.addWidget(table, 1)

        def take_live():
            for fixture in self.show_data["fixtures"]:
                for key in keys:
                    spinboxes[(fixture["id"], key)].setValue(int(fixture.get("look", {}).get(key, 0)))

        footer = QHBoxLayout()
        live_button = button("Взять из LIVE", take_live); footer.addWidget(live_button)
        footer.addStretch(1)
        cancel = button("Отмена"); cancel.clicked.connect(dialog.reject); footer.addWidget(cancel)
        save = button("Сохранить snapshot", primary=True); save.clicked.connect(dialog.accept); footer.addWidget(save)
        box.addLayout(footer)
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return

        candidate = copy.deepcopy(self.show_data)
        updated_cue = next(item for item in candidate["cues"] if item["id"] == cue["id"])
        updated_cue["label"] = name.text().strip() or cue.get("label", "Snapshot")
        updated_cue["fade"] = fade.value()
        updated_cue["stage_layout_id"] = layout_picker.currentData()
        updated_cue["look"] = {fixture["id"]: {key: spinboxes[(fixture["id"], key)].value() for key in keys}
                                for fixture in candidate["fixtures"]}
        scene = next((item for item in candidate["scenes"] if item["id"] == updated_cue.get("scene_id")), None)
        if scene:
            scene["name"] = updated_cue["label"]
            scene["look"] = copy.deepcopy(updated_cue["look"])
        try:
            ShowSchema.validate(candidate)
        except ValueError as exc:
            QMessageBox.warning(self, "Snapshot", str(exc))
            return
        self._checkpoint(); self.show_data = candidate; self.dirty = True; self.refresh_all()

    def _selected_cue(self):
        item = self.cue_list.currentItem()
        cue_id = self.preview_cue_id or (item.data(Qt.ItemDataRole.UserRole) if item else None)
        return next((cue for cue in self.show_data["cues"] if cue.get("id") == cue_id), None)

    def _delete_cue(self):
        cue = self._selected_cue()
        if not cue: return
        self._checkpoint(); self.show_data["cues"].remove(cue)
        if not any(c.get("scene_id") == cue.get("scene_id") for c in self.show_data["cues"]):
            self.show_data["scenes"] = [s for s in self.show_data["scenes"] if s.get("id") != cue.get("scene_id")]
        self.preview_cue_id = None; self.dirty = True; self.refresh_all()

    def fire_cue(self):
        cue = self._selected_cue()
        if not cue:
            QMessageBox.information(self, "Snapshot", "Сначала выберите snapshot для FIRE.")
            return
        self._cancel_fade()
        self._checkpoint()
        layout_id = cue.get("stage_layout_id")
        if layout_id and layout_id != self.show_data["stage"].get("active_layout_id"):
            self._activate_stage_layout(layout_id, mark_dirty=False)
        self.live_cue_id = cue["id"]
        look = cue.get("look", {})
        start = {fixture["id"]: copy.deepcopy(fixture.get("look", blank_look()))
                 for fixture in self.show_data["fixtures"]}
        end = {fixture["id"]: copy.deepcopy(look.get(fixture["id"], start[fixture["id"]]))
               for fixture in self.show_data["fixtures"]}
        duration = max(0.0, min(600.0, float(cue.get("fade", 0))))
        self.refresh_all()
        if duration > 0:
            self._fade = {"started": time.monotonic(), "duration": duration, "start": start, "end": end,
                          "label": cue.get("label", "Snapshot")}
            self.fade_timer.start()
            self._tick_fade()
        else:
            for fixture in self.show_data["fixtures"]:
                fixture["look"] = end[fixture["id"]]
            self._send_dmx(); self.refresh_stage_views()
            self.status_bar.setText(f"LIVE · {cue.get('label', 'Snapshot')} вызван")
        if self.auto_next.isChecked():
            index = self.show_data["cues"].index(cue)
            self.preview_cue_id = self.show_data["cues"][(index + 1) % len(self.show_data["cues"])]["id"]
            self.refresh_all()

    def _cancel_fade(self):
        if self.fade_timer.isActive(): self.fade_timer.stop()
        self._fade = None

    def _tick_fade(self):
        fade = self._fade
        if not fade: return
        amount = min(1.0, (time.monotonic() - fade["started"]) / fade["duration"])
        eased = amount * amount * (3 - 2 * amount)
        for fixture in self.show_data["fixtures"]:
            fid = fixture["id"]
            start = fade["start"].get(fid, blank_look())
            end = fade["end"].get(fid, blank_look())
            fixture["look"] = {key: round(start.get(key, 0) + (end.get(key, 0) - start.get(key, 0)) * eased)
                                for key in ("dimmer", "r", "g", "b", "w")}
        self.dirty = True
        self._fixture_selection_from_ids(); self.refresh_stage_views(); self._send_dmx()
        if amount >= 1:
            self._cancel_fade()
            self.status_bar.setText(f"LIVE · {fade['label']} · переход завершён")
        else:
            self.status_bar.setText(f"LIVE · {fade['label']} · переход {round(amount * 100)}%")

    def previous_cue(self):
        cues = self.show_data["cues"]
        if not cues: return
        current = next((i for i, cue in enumerate(cues) if cue["id"] == self.live_cue_id), 0)
        self.preview_cue_id = cues[max(0, current - 1)]["id"]
        self.refresh_all()

    def refresh_stage_views(self):
        if not hasattr(self, "live_stage"):
            return
        editor_selection = {item.data.get("id") for item in self.editor_stage.stage.selectedItems()
                            if isinstance(item, StageObject)}
        self._ensure_stage_fixtures()
        blackout_look = ({f["id"]: {"dimmer": 0, "r": 0, "g": 0, "b": 0, "w": 0}
                          for f in self.show_data.get("fixtures", [])} if self.blackout_active else None)
        live_cue = next((c for c in self.show_data["cues"] if c.get("id") == self.live_cue_id), None)
        cue = next((c for c in self.show_data["cues"] if c.get("id") == self.preview_cue_id), None)
        live_plan = self._stage_show_for_layout(live_cue.get("stage_layout_id") if live_cue else None)
        preview_plan = self._stage_show_for_layout(cue.get("stage_layout_id") if cue else None)
        self.live_stage.set_data(live_plan, look=blackout_look, selected_id=self.selected_stage_id, readonly=True)
        self.editor_stage.set_data(self.show_data, selected_id=self.selected_stage_id)
        for item in self.editor_stage.stage.items():
            if isinstance(item, StageObject) and item.data.get("id") in editor_selection:
                item.setSelected(True)
        self.cue_live_stage.set_data(live_plan, look=blackout_look, readonly=True)
        self.cue_stage.set_data(preview_plan, look=cue.get("look", {}) if cue else {}, readonly=True)

    def _stage_show_for_layout(self, layout_id):
        result = dict(self.show_data)
        stage = copy.deepcopy(self.show_data.get("stage", {}))
        layout = next((entry for entry in stage.get("layouts", []) if entry.get("id") == layout_id), None)
        if layout:
            stage["objects"] = copy.deepcopy(layout.get("objects", []))
            stage["active_layout_id"] = layout_id
        result["stage"] = stage
        return result

    def _ensure_stage_fixtures(self):
        stage = self.show_data.setdefault("stage", {"width_m": 8, "depth_m": 6, "objects": []})
        objects = stage.setdefault("objects", [])
        fixtures_by_id = {fixture["id"]: fixture for fixture in self.show_data.get("fixtures", [])}
        for item in objects:
            fixture = fixtures_by_id.get(item.get("fixture_id")) if item.get("kind") == "fixture" else None
            if fixture:
                item["label"] = fixture.get("name", item.get("label", "PAR"))
        placed = {item.get("fixture_id") for item in objects if item.get("kind") == "fixture"}
        fixtures = [fixture for fixture in self.show_data.get("fixtures", []) if fixture["id"] not in placed]
        count = len(fixtures)
        for index, fixture in enumerate(fixtures):
            objects.append({"id": new_id(), "kind": "fixture", "fixture_id": fixture["id"],
                            "label": fixture.get("name", "PAR"), "x": .14 + .72 * index / max(1, count - 1),
                            "y": .15, "w": .07, "h": .11, "color": AMBER})
        self._ensure_stage_layouts()

    def _stage_selected(self, object_id):
        self.selected_stage_id = object_id
        obj = self._selected_stage_object()
        if obj and obj.get("kind") == "fixture":
            fixture_id = obj.get("fixture_id")
            self.selected_fixture_ids = {fixture_id}
            self.fixture_list.blockSignals(True)
            for index in range(self.fixture_list.count()):
                item = self.fixture_list.item(index)
                item.setSelected(item.data(Qt.ItemDataRole.UserRole) == fixture_id)
            self.fixture_list.blockSignals(False)
            self._fixture_selection_from_ids()
        else:
            for view_name in ("live_stage", "editor_stage", "cue_live_stage", "cue_stage"):
                view = getattr(self, view_name, None)
                if view: view.set_selected(object_id)
        self._sync_stage_inspector()

    def refresh_all(self):
        if not hasattr(self, "fixture_list"):
            return
        self.show_name.setText(self.show_data["name"] + ("  •" if self.dirty else ""))
        self.fixture_list.blockSignals(True); self.fixture_list.clear()
        member_of = {fid: gang.get("name", "GANG") for gang in self.show_data.get("gangs", []) for fid in gang.get("members", [])}
        for fixture in self.show_data.get("fixtures", []):
            status = f"     ·     {member_of[fixture['id']]}" if fixture["id"] in member_of else ""
            if fixture["id"] in self.gang_isolated_ids: status += " · ISO"
            item = QListWidgetItem(f"{fixture['name']}     ·     {fixture['address']:03d}{status}")
            item.setData(Qt.ItemDataRole.UserRole, fixture["id"])
            self.fixture_list.addItem(item)
            if fixture["id"] in self.selected_fixture_ids: item.setSelected(True)
        self.fixture_list.blockSignals(False)
        self._patch_sync = True
        self.patch_table.setRowCount(len(self.show_data.get("fixtures", [])))
        for row, fixture in enumerate(self.show_data.get("fixtures", [])):
            for col, value in enumerate((fixture["name"], str(fixture["address"]), fixture.get("group", "Сцена"), "RGBW")):
                cell = QTableWidgetItem(value)
                if col == 3: cell.setFlags(cell.flags() & ~Qt.ItemFlag.ItemIsEditable)
                self.patch_table.setItem(row, col, cell)
        self._patch_sync = False
        self.cue_list.clear()
        for index, cue in enumerate(self.show_data.get("cues", []), start=1):
            live_status = "    ·    В ЭФИРЕ" if cue.get("id") == self.live_cue_id else ""
            scene_number = self._scene_number_for_cue(cue)
            full = QListWidgetItem(f"SNAPSHOT {index:02d}  ·  СЦЕНА {scene_number:02d}  ·  {cue.get('label', 'Snapshot')}  ·  {cue.get('fade', 0):g} с{live_status}")
            full.setToolTip(f"Snapshot {index:02d} · сцена {scene_number:02d} · {cue.get('label', 'Snapshot')} · переход {float(cue.get('fade', 0)):g} с")
            full.setData(Qt.ItemDataRole.UserRole, cue["id"]); self.cue_list.addItem(full)
        self.stage_width.blockSignals(True); self.stage_depth.blockSignals(True)
        self.stage_width.setValue(self.show_data["stage"].get("width_m", 8)); self.stage_depth.setValue(self.show_data["stage"].get("depth_m", 6))
        self.stage_width.blockSignals(False); self.stage_depth.blockSignals(False)
        live_cue = next((cue for cue in self.show_data["cues"] if cue["id"] == self.live_cue_id), None)
        if live_cue:
            self.live_label.setText(f"LIVE · SNAPSHOT {self._cue_number_for(live_cue):02d} · СЦЕНА {self._scene_number_for_cue(live_cue):02d} · {live_cue['label']}")
        else:
            self.live_label.setText("LIVE · НЕТ ВЫЗВАННОГО SNAPSHOT")
        self._refresh_gangs()
        self.refresh_stage_views(); self._sync_stage_inspector(); self._fixture_selection()
        if self.preview_cue_id:
            item = next((self.cue_list.item(i) for i in range(self.cue_list.count()) if self.cue_list.item(i).data(Qt.ItemDataRole.UserRole) == self.preview_cue_id), None)
            if item: self.cue_list.setCurrentItem(item)
        self._update_cue_preview_label()

    def _checkpoint(self):
        state = copy.deepcopy(self.show_data)
        if not self.undo_stack or self.undo_stack[-1] != state: self.undo_stack.append(state)
        self.undo_stack = self.undo_stack[-100:]; self.redo_stack.clear()

    def undo(self):
        self._cancel_fade()
        if self.undo_stack:
            self.redo_stack.append(copy.deepcopy(self.show_data)); self.show_data = self.undo_stack.pop(); self.dirty = True; self.refresh_all()
    def redo(self):
        self._cancel_fade()
        if self.redo_stack:
            self.undo_stack.append(copy.deepcopy(self.show_data)); self.show_data = self.redo_stack.pop(); self.dirty = True; self.refresh_all()

    def _new_show(self):
        if not self._confirm_unsaved(): return
        self._cancel_fade()
        self.show_data = default_show(); self.show_path = None; self.dirty = False; self.live_cue_id = None; self.preview_cue_id = None
        self.selected_fixture_ids = {self.show_data["fixtures"][0]["id"]}; self.undo_stack.clear(); self.redo_stack.clear(); self.refresh_all()

    def _open_dialog(self):
        if not self._confirm_unsaved(): return
        path, _ = QFileDialog.getOpenFileName(self, "Открыть шоу", "", "Шоу OLEG (*.dmxshow *.json);;Все файлы (*)")
        if not path: return
        try:
            with open(path, "r", encoding="utf-8") as file: data = json.load(file)
            ShowSchema.migrate(data)
            ShowSchema.validate(data)
            self._cancel_fade()
            self.show_data = data; self.show_path = Path(path); self.dirty = False
            self.selected_fixture_ids = {data["fixtures"][0]["id"]} if data["fixtures"] else set()
            self.preview_cue_id = data["cues"][0]["id"] if data["cues"] else None
            self.undo_stack.clear(); self.redo_stack.clear(); self.refresh_all()
            self.status_bar.setText(f"Открыто локально · {self.show_path.name}")
        except Exception as exc: QMessageBox.critical(self, "Открыть шоу", str(exc))

    def _confirm_unsaved(self):
        if not self.dirty: return True
        answer = QMessageBox.warning(
            self, "Несохранённые изменения",
            "Сохранить изменения в текущем шоу перед продолжением?",
            QMessageBox.StandardButton.Save | QMessageBox.StandardButton.Discard | QMessageBox.StandardButton.Cancel,
            QMessageBox.StandardButton.Save,
        )
        if answer == QMessageBox.StandardButton.Cancel: return False
        if answer == QMessageBox.StandardButton.Save:
            self._save_dialog()
            return not self.dirty
        return True

    def _save_dialog(self):
        path = self.show_path
        if path is None:
            filename, _ = QFileDialog.getSaveFileName(self, "Сохранить шоу", f"{self.show_data['name'].replace(' ', '_')}.dmxshow", "Шоу OLEG (*.dmxshow)")
            if not filename: return
            path = Path(filename)
            if path.suffix.lower() != ".dmxshow": path = path.with_suffix(".dmxshow")
        try:
            data = copy.deepcopy(self.show_data)
            ShowSchema.validate(data)
            data["name"] = path.stem.replace("_", " ")
            path.parent.mkdir(parents=True, exist_ok=True)
            temp = path.with_suffix(path.suffix + ".tmp")
            temp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            if path.exists(): path.with_suffix(path.suffix + ".bak").write_bytes(path.read_bytes())
            temp.replace(path)
            self.show_path = path; self.show_data["name"] = data["name"]; self.dirty = False
            self.refresh_all(); self.status_bar.setText(f"Сохранено локально · {path.name}")
        except Exception as exc: QMessageBox.critical(self, "Сохранить шоу", str(exc))


def launch():
    app = QApplication.instance() or QApplication([])
    app.setApplicationName(APP_NAME)
    app.setStyle("Fusion")
    windows_font = Path("C:/Windows/Fonts/segoeui.ttf")
    if windows_font.exists():
        QFontDatabase.addApplicationFont(str(windows_font))
    app.setFont(QFont("Segoe UI", 10))
    window = OlegWindow()
    window.show()
    app.exec()

