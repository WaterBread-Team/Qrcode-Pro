import tkinter as tk
from tkinter import ttk, messagebox, filedialog, colorchooser
import qrcode
from PIL import Image, ImageTk, ImageDraw, ImageFilter, ImageFont
import io
import os
import json
import re
from collections import Counter
from datetime import datetime, timedelta
from urllib.parse import urlparse

# Intento importar lector QR (opcional)
try:
    from pyzbar.pyzbar import decode as pyzbar_decode
    PYZBAR_OK = True
except ImportError:
    PYZBAR_OK = False

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    TKDND_OK = True
except ImportError:
    DND_FILES = None
    TkinterDnD = None
    TKDND_OK = False

CONFIG_FILE = os.path.join(os.path.expanduser("~"), ".qr_pro_config.json")

# ══════════════════════════════════════════════════════════════
#  TEMAS
# ══════════════════════════════════════════════════════════════

DARK = {
    "bg":           "#1e1e2e",
    "bg2":          "#181825",
    "sidebar":      "#11111b",
    "card":         "#252530",
    "card2":        "#2d2f3a",
    "fg":           "#cdd6f4",
    "entry_bg":     "#313244",
    "btn_bg":       "#45475a",
    "border":       "#585b70",
    "green":        "#a6e3a1",
    "blue":         "#89b4fa",
    "red":          "#f38ba8",
    "purple":       "#cba6f7",
    "yellow":       "#f9e2af",
    "subtext":      "#6c7086",
    "check_sel":    "#313244",
}
LIGHT = {
    "bg":           "#f0f2f5",
    "bg2":          "#ffffff",
    "sidebar":      "#e7ebf2",
    "card":         "#ffffff",
    "card2":        "#eef2f8",
    "fg":           "#1e1e2e",
    "entry_bg":     "#ffffff",
    "btn_bg":       "#dde1e9",
    "border":       "#b0b8c8",
    "green":        "#2e7d32",
    "blue":         "#1565C0",
    "red":          "#b71c1c",
    "purple":       "#6A1B9A",
    "yellow":       "#f57f17",
    "subtext":      "#666680",
    "check_sel":    "#ffffff",
}

# Colores de acento independientes del tema (para botones)
BTN_GREEN_D,  BTN_GREEN_L  = "#22c55e", "#16a34a"
BTN_BLUE_D,   BTN_BLUE_L   = "#3b82f6", "#2563eb"
BTN_RED_D,    BTN_RED_L    = "#fb7185", "#dc2626"
BTN_PURPLE_D, BTN_PURPLE_L = "#a855f7", "#7c3aed"
BTN_GREY_D,   BTN_GREY_L   = "#64748b", "#475569"
BTN_TEAL_D,   BTN_TEAL_L   = "#14b8a6", "#0f766e"


def blend_hex(start: str, end: str, ratio: float) -> str:
    ratio = max(0.0, min(1.0, ratio))

    def to_rgb(color: str) -> tuple[int, int, int]:
        color = color.lstrip("#")
        return tuple(int(color[i:i + 2], 16) for i in (0, 2, 4))

    start_rgb = to_rgb(start)
    end_rgb = to_rgb(end)
    mixed = tuple(int(start_rgb[i] + (end_rgb[i] - start_rgb[i]) * ratio) for i in range(3))
    return "#{:02x}{:02x}{:02x}".format(*mixed)


def shift_hex(color: str, amount: float) -> str:
    target = "#ffffff" if amount >= 0 else "#000000"
    return blend_hex(color, target, abs(amount))


# ══════════════════════════════════════════════════════════════
#  LÓGICA QR (sin UI)
# ══════════════════════════════════════════════════════════════

class QREngine:
    CORRECTION_LEVELS = {
        "L – Baja (7%)":   qrcode.constants.ERROR_CORRECT_L,
        "M – Media (15%)": qrcode.constants.ERROR_CORRECT_M,
        "Q – Alta (25%)":  qrcode.constants.ERROR_CORRECT_Q,
        "H – Máxima (30%)":qrcode.constants.ERROR_CORRECT_H,
    }
    SIZE_MAP = {"Pequeño": 6, "Mediano": 10, "Grande": 14}
    BARCODE_FORMATS = ["Code 39", "EAN-13", "EAN-8", "UPC-A", "ITF"]
    BARCODE_WIDTH_MAP = {"Fino": 2, "Normal": 3, "Grueso": 4}
    BARCODE_HEIGHT_MAP = {"Bajo": 90, "Medio": 130, "Alto": 170}
    EAN_L_CODES = {
        "0": "0001101", "1": "0011001", "2": "0010011", "3": "0111101", "4": "0100011",
        "5": "0110001", "6": "0101111", "7": "0111011", "8": "0110111", "9": "0001011",
    }
    EAN_G_CODES = {
        "0": "0100111", "1": "0110011", "2": "0011011", "3": "0100001", "4": "0011101",
        "5": "0111001", "6": "0000101", "7": "0010001", "8": "0001001", "9": "0010111",
    }
    EAN_R_CODES = {
        "0": "1110010", "1": "1100110", "2": "1101100", "3": "1000010", "4": "1011100",
        "5": "1001110", "6": "1010000", "7": "1000100", "8": "1001000", "9": "1110100",
    }
    EAN13_PARITY = {
        "0": "LLLLLL", "1": "LLGLGG", "2": "LLGGLG", "3": "LLGGGL", "4": "LGLLGG",
        "5": "LGGLLG", "6": "LGGGLL", "7": "LGLGLG", "8": "LGLGGL", "9": "LGGLGL",
    }
    CODE39_PATTERNS = {
        "0": "nnnwwnwnn", "1": "wnnwnnnnw", "2": "nnwwnnnnw", "3": "wnwwnnnnn",
        "4": "nnnwwnnnw", "5": "wnnwwnnnn", "6": "nnwwwnnnn", "7": "nnnwnnwnw",
        "8": "wnnwnnwnn", "9": "nnwwnnwnn", "A": "wnnnnwnnw", "B": "nnwnnwnnw",
        "C": "wnwnnwnnn", "D": "nnnnwwnnw", "E": "wnnnwwnnn", "F": "nnwnwwnnn",
        "G": "nnnnnwwnw", "H": "wnnnnwwnn", "I": "nnwnnwwnn", "J": "nnnnwwwnn",
        "K": "wnnnnnnww", "L": "nnwnnnnww", "M": "wnwnnnnwn", "N": "nnnnwnnww",
        "O": "wnnnwnnwn", "P": "nnwnwnnwn", "Q": "nnnnnnwww", "R": "wnnnnnwwn",
        "S": "nnwnnnwwn", "T": "nnnnwnwwn", "U": "wwnnnnnnw", "V": "nwwnnnnnw",
        "W": "wwwnnnnnn", "X": "nwnnwnnnw", "Y": "wwnnwnnnn", "Z": "nwwnwnnnn",
        "-": "nwnnnnwnw", ".": "wwnnnnwnn", " ": "nwwnnnwnn", "$": "nwnwnwnnn",
        "/": "nwnwnnnwn", "+": "nwnnnwnwn", "%": "nnnwnwnwn", "*": "nwnnwnwnn",
    }
    ITF_PATTERNS = {
        "0": "nnwwn", "1": "wnnnw", "2": "nwnnw", "3": "wwnnn", "4": "nnwnw",
        "5": "wnwnn", "6": "nwwnn", "7": "nnnww", "8": "wnnwn", "9": "nwnwn",
    }

    @staticmethod
    def detect_type(text: str) -> str:
        t = text.strip()
        if re.match(r"^(https?://|www\.)", t, re.I): return "URL"
        if t.upper().startswith("WIFI:"): return "WiFi"
        if t.upper().startswith("MAILTO:") or re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", t): return "Email"
        if t.upper().startswith("BEGIN:VCARD"): return "vCard"
        if re.match(r"^\+?[\d\s\-()]{7,}$", t): return "Teléfono"
        return "Texto"

    @staticmethod
    def generate(
        data: str,
        fill_color: str = "black",
        back_color: str = "white",
        box_size: int = 10,
        border: int = 4,
        error_correction=qrcode.constants.ERROR_CORRECT_H,
        invert: bool = False,
        show_border: bool = True,
        logo_path: str = None,
        style: str = "Clásico",
    ) -> Image.Image:

        if invert:
            fill_color, back_color = back_color, fill_color

        qr = qrcode.QRCode(
            version=1,
            error_correction=error_correction,
            box_size=box_size,
            border=border if show_border else 0,
        )
        qr.add_data(data)
        qr.make(fit=True)

        if style == "Puntos":
            img = QREngine._make_dots(qr, fill_color, back_color)
        elif style == "Redondeado":
            img = QREngine._make_rounded(qr, fill_color, back_color)
        else:
            img = qr.make_image(fill_color=fill_color, back_color=back_color).convert("RGBA")

        if logo_path and os.path.isfile(logo_path):
            try:
                logo = Image.open(logo_path).convert("RGBA")
                qr_w, qr_h = img.size
                max_logo = qr_w // 4
                logo.thumbnail((max_logo, max_logo), Image.Resampling.LANCZOS)
                lw, lh = logo.size
                pos = ((qr_w - lw) // 2, (qr_h - lh) // 2)
                bg = Image.new("RGBA", (lw + 14, lh + 14), (255, 255, 255, 255))
                img.paste(bg, (pos[0] - 7, pos[1] - 7))
                img.paste(logo, pos, mask=logo)
            except Exception:
                pass

        return img

    @staticmethod
    def detect_barcode_type(barcode_format: str) -> str:
        return f"Código de barras · {barcode_format}"

    @staticmethod
    def normalize_barcode_data(data: str, barcode_format: str) -> str:
        barcode_format = barcode_format.strip()
        cleaned = data.strip().upper()

        if barcode_format == "Code 39":
            allowed = set("0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ-. $/+%")
            if not cleaned:
                raise ValueError("Escribe un valor para el código de barras.")
            if any(ch not in allowed for ch in cleaned):
                raise ValueError("Code 39 solo admite A-Z, 0-9 y los símbolos - . espacio $ / + %")
            return cleaned

        digits = re.sub(r"\D", "", cleaned)
        if not digits:
            raise ValueError("Este formato de barras necesita datos numéricos.")

        if barcode_format == "EAN-13":
            return QREngine._normalize_gtin(digits, 13)
        if barcode_format == "EAN-8":
            return QREngine._normalize_gtin(digits, 8)
        if barcode_format == "UPC-A":
            return QREngine._normalize_gtin(digits, 12)
        if barcode_format == "ITF":
            return digits if len(digits) % 2 == 0 else f"0{digits}"

        raise ValueError(f"Formato de barras no soportado: {barcode_format}")

    @staticmethod
    def generate_barcode(
        data: str,
        barcode_format: str = "Code 39",
        fill_color: str = "black",
        back_color: str = "white",
        module_width: int = 3,
        height: int = 130,
        show_text: bool = True,
    ) -> Image.Image:
        normalized = QREngine.normalize_barcode_data(data, barcode_format)

        if barcode_format == "Code 39":
            return QREngine._draw_width_pattern(
                QREngine._encode_code39(normalized),
                normalized,
                module_width,
                height,
                fill_color,
                back_color,
                show_text,
            )
        if barcode_format == "ITF":
            return QREngine._draw_width_pattern(
                QREngine._encode_itf(normalized),
                normalized,
                module_width,
                height,
                fill_color,
                back_color,
                show_text,
            )
        if barcode_format == "UPC-A":
            bits = QREngine._encode_ean13_bits(f"0{normalized}")
            return QREngine._draw_binary_pattern(bits, normalized, module_width, height, fill_color, back_color, show_text)
        if barcode_format == "EAN-13":
            bits = QREngine._encode_ean13_bits(normalized)
            return QREngine._draw_binary_pattern(bits, normalized, module_width, height, fill_color, back_color, show_text)
        if barcode_format == "EAN-8":
            bits = QREngine._encode_ean8_bits(normalized)
            return QREngine._draw_binary_pattern(bits, normalized, module_width, height, fill_color, back_color, show_text)

        raise ValueError(f"Formato de barras no soportado: {barcode_format}")

    @staticmethod
    def _hex_to_rgb(hex_c: str):
        hex_c = hex_c.lstrip("#")
        return tuple(int(hex_c[i:i+2], 16) for i in (0, 2, 4))

    @staticmethod
    def _make_dots(qr, fill_color, back_color):
        matrix = qr.get_matrix()
        n = len(matrix)
        box = qr.box_size
        size = n * box
        img = Image.new("RGBA", (size, size),
                        QREngine._hex_to_rgb(back_color) if back_color.startswith("#") else back_color)
        draw = ImageDraw.Draw(img)
        fc = QREngine._hex_to_rgb(fill_color) if fill_color.startswith("#") else fill_color
        for r, row in enumerate(matrix):
            for c, val in enumerate(row):
                if val:
                    x0 = c * box + 1
                    y0 = r * box + 1
                    x1 = x0 + box - 2
                    y1 = y0 + box - 2
                    draw.ellipse([x0, y0, x1, y1], fill=fc)
        return img

    @staticmethod
    def _make_rounded(qr, fill_color, back_color):
        matrix = qr.get_matrix()
        n = len(matrix)
        box = qr.box_size
        size = n * box
        img = Image.new("RGBA", (size, size),
                        QREngine._hex_to_rgb(back_color) if back_color.startswith("#") else back_color)
        draw = ImageDraw.Draw(img)
        fc = QREngine._hex_to_rgb(fill_color) if fill_color.startswith("#") else fill_color
        r_val = box // 3
        for r, row in enumerate(matrix):
            for c, val in enumerate(row):
                if val:
                    x0, y0 = c * box, r * box
                    x1, y1 = x0 + box - 1, y0 + box - 1
                    draw.rounded_rectangle([x0, y0, x1, y1], radius=r_val, fill=fc)
        return img

    @staticmethod
    def scan_image(path: str) -> list[dict]:
        if not PYZBAR_OK:
            return []
        try:
            img = Image.open(path)
            results = pyzbar_decode(img)
            return [
                {
                    "type": getattr(r, "type", "Código"),
                    "text": r.data.decode("utf-8", errors="replace"),
                }
                for r in results
            ]
        except Exception:
            return []

    @staticmethod
    def _normalize_gtin(digits: str, total_length: int) -> str:
        base_length = total_length - 1
        if len(digits) == base_length:
            return digits + QREngine._gtin_checksum(digits)
        if len(digits) == total_length:
            expected = QREngine._gtin_checksum(digits[:-1])
            if digits[-1] != expected:
                raise ValueError(f"Dígito verificador inválido. Debe terminar en {expected}.")
            return digits
        raise ValueError(f"Este formato requiere {base_length} o {total_length} dígitos.")

    @staticmethod
    def _gtin_checksum(digits: str) -> str:
        total = 0
        for idx, digit in enumerate(reversed(digits), start=1):
            total += int(digit) * (3 if idx % 2 == 1 else 1)
        return str((10 - total % 10) % 10)

    @staticmethod
    def _encode_ean13_bits(digits: str) -> str:
        parity = QREngine.EAN13_PARITY[digits[0]]
        left = "".join(
            QREngine.EAN_L_CODES[d] if p == "L" else QREngine.EAN_G_CODES[d]
            for d, p in zip(digits[1:7], parity)
        )
        right = "".join(QREngine.EAN_R_CODES[d] for d in digits[7:])
        return f"101{left}01010{right}101"

    @staticmethod
    def _encode_ean8_bits(digits: str) -> str:
        left = "".join(QREngine.EAN_L_CODES[d] for d in digits[:4])
        right = "".join(QREngine.EAN_R_CODES[d] for d in digits[4:])
        return f"101{left}01010{right}101"

    @staticmethod
    def _encode_code39(data: str) -> list[tuple[bool, int]]:
        sequence: list[tuple[bool, int]] = []
        payload = f"*{data}*"
        for index, ch in enumerate(payload):
            pattern = QREngine.CODE39_PATTERNS[ch]
            for part_index, part in enumerate(pattern):
                sequence.append((part_index % 2 == 0, 3 if part == "w" else 1))
            if index < len(payload) - 1:
                sequence.append((False, 1))
        return sequence

    @staticmethod
    def _encode_itf(digits: str) -> list[tuple[bool, int]]:
        sequence: list[tuple[bool, int]] = []
        start = "nnnn"
        end = "wnn"
        for index, part in enumerate(start):
            sequence.append((index % 2 == 0, 3 if part == "w" else 1))

        for first, second in zip(digits[::2], digits[1::2]):
            bars = QREngine.ITF_PATTERNS[first]
            spaces = QREngine.ITF_PATTERNS[second]
            for bar, space in zip(bars, spaces):
                sequence.append((True, 3 if bar == "w" else 1))
                sequence.append((False, 3 if space == "w" else 1))

        end_bars = [(True, 3 if end[0] == "w" else 1), (False, 3 if end[1] == "w" else 1), (True, 3 if end[2] == "w" else 1)]
        sequence.extend(end_bars)
        return sequence

    @staticmethod
    def _measure_label(label: str, font) -> tuple[int, int]:
        dummy = Image.new("RGB", (8, 8), "white")
        draw = ImageDraw.Draw(dummy)
        left, top, right, bottom = draw.textbbox((0, 0), label, font=font)
        return right - left, bottom - top

    @staticmethod
    def _draw_binary_pattern(bits: str, label: str, module_width: int, height: int,
                             fill_color: str, back_color: str, show_text: bool) -> Image.Image:
        quiet = module_width * 10
        font = ImageFont.load_default()
        text_w, text_h = QREngine._measure_label(label, font) if show_text and label else (0, 0)
        total_h = height + (text_h + 10 if show_text and label else 0)
        width = len(bits) * module_width + quiet * 2
        img = Image.new("RGBA", (width, total_h), back_color)
        draw = ImageDraw.Draw(img)

        x = quiet
        for bit in bits:
            if bit == "1":
                draw.rectangle([x, 0, x + module_width - 1, height], fill=fill_color)
            x += module_width

        if show_text and label:
            draw.text(((width - text_w) // 2, height + 4), label, fill=fill_color, font=font)
        return img

    @staticmethod
    def _draw_width_pattern(sequence: list[tuple[bool, int]], label: str, module_width: int, height: int,
                            fill_color: str, back_color: str, show_text: bool) -> Image.Image:
        quiet = module_width * 10
        font = ImageFont.load_default()
        text_w, text_h = QREngine._measure_label(label, font) if show_text and label else (0, 0)
        total_h = height + (text_h + 10 if show_text and label else 0)
        width = quiet * 2 + sum(units for _, units in sequence) * module_width
        img = Image.new("RGBA", (width, total_h), back_color)
        draw = ImageDraw.Draw(img)

        x = quiet
        for is_bar, units in sequence:
            bar_width = units * module_width
            if is_bar:
                draw.rectangle([x, 0, x + bar_width - 1, height], fill=fill_color)
            x += bar_width

        if show_text and label:
            draw.text(((width - text_w) // 2, height + 4), label, fill=fill_color, font=font)
        return img

    # ── Builders de tipos especiales ───────────────────────────────────────

    @staticmethod
    def build_wifi(ssid, password, security="WPA", hidden=False):
        h = "true" if hidden else "false"
        return f"WIFI:T:{security};S:{ssid};P:{password};H:{h};;"

    @staticmethod
    def build_email(address, subject="", body=""):
        parts = []
        if subject: parts.append(f"subject={subject}")
        if body: parts.append(f"body={body}")
        query = "&".join(parts)
        return f"mailto:{address}{'?' + query if query else ''}"

    @staticmethod
    def build_vcard(name, phone, email="", org="", url=""):
        lines = ["BEGIN:VCARD", "VERSION:3.0", f"FN:{name}"]
        if phone: lines.append(f"TEL:{phone}")
        if email: lines.append(f"EMAIL:{email}")
        if org: lines.append(f"ORG:{org}")
        if url: lines.append(f"URL:{url}")
        lines.append("END:VCARD")
        return "\n".join(lines)


# ══════════════════════════════════════════════════════════════
#  CONFIGURACIÓN PERSISTENTE
# ══════════════════════════════════════════════════════════════

class AppConfig:
    KEYS = ["fill_color", "back_color", "size_name", "correction_name",
            "show_border", "invert", "include_logo", "logo_path",
            "dark_theme", "qr_style", "content_mode", "barcode_format",
            "barcode_width_name", "barcode_height_name", "barcode_show_text",
            "last_text"]

    def __init__(self):
        self.fill_color      = "#000000"
        self.back_color      = "#ffffff"
        self.size_name       = "Mediano"
        self.correction_name = "H – Máxima (30%)"
        self.show_border     = True
        self.invert          = False
        self.include_logo    = False
        self.logo_path       = ""
        self.dark_theme      = False
        self.qr_style        = "Clásico"
        self.content_mode    = "QR"
        self.barcode_format  = "Code 39"
        self.barcode_width_name = "Normal"
        self.barcode_height_name = "Medio"
        self.barcode_show_text = True
        self.last_text        = ""
        self.history: list[dict] = []
        self.max_history     = 25
        self.presets: list[dict] = []
        self.load()

    def save(self):
        try:
            data = {k: getattr(self, k) for k in self.KEYS}
            data["history_meta"] = [
                {"text": e["text"], "type": e["type"], "timestamp": e["timestamp"]}
                for e in self.history
            ]
            data["presets"] = self.presets
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception:
            pass

    def load(self):
        try:
            if not os.path.isfile(CONFIG_FILE):
                return
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            for k in self.KEYS:
                if k in data:
                    setattr(self, k, data[k])
            for entry in data.get("history_meta", []):
                self.history.append({
                    "text": entry.get("text", ""),
                    "type": entry.get("type", "Texto"),
                    "timestamp": entry.get("timestamp", ""),
                    "img_bytes": None,
                })
            self.presets = data.get("presets", [])
        except Exception:
            pass

    def add_to_history(self, text: str, dtype: str, img: Image.Image):
        buf = io.BytesIO()
        img.save(buf, format="PNG")
        # Evitar duplicado consecutivo
        if self.history and self.history[0]["text"] == text and self.history[0]["type"] == dtype:
            self.history[0]["img_bytes"] = buf.getvalue()
            self.history[0]["timestamp"] = datetime.now().strftime("%d/%m/%Y %H:%M")
        else:
            entry = {"text": text, "type": dtype,
                     "timestamp": datetime.now().strftime("%d/%m/%Y %H:%M"),
                     "img_bytes": buf.getvalue()}
            self.history.insert(0, entry)
            if len(self.history) > self.max_history:
                self.history.pop()
        self.save()

    def save_preset(self, name: str):
        preset = {k: getattr(self, k) for k in
                  ["fill_color","back_color","size_name","correction_name",
                   "show_border","invert","include_logo","logo_path","qr_style",
                   "content_mode","barcode_format","barcode_width_name",
                   "barcode_height_name","barcode_show_text"]}
        preset["name"] = name
        self.presets = [p for p in self.presets if p["name"] != name]
        self.presets.insert(0, preset)
        self.presets = self.presets[:10]
        self.save()

    def load_preset(self, name: str) -> bool:
        for p in self.presets:
            if p["name"] == name:
                for k in ["fill_color","back_color","size_name","correction_name",
                           "show_border","invert","include_logo","logo_path","qr_style",
                           "content_mode","barcode_format","barcode_width_name",
                           "barcode_height_name","barcode_show_text"]:
                    if k in p:
                        setattr(self, k, p[k])
                return True
        return False


# ══════════════════════════════════════════════════════════════
#  VENTANAS AUXILIARES
# ══════════════════════════════════════════════════════════════

class OptionsWindow(tk.Toplevel):
    STYLES = ["Clásico", "Puntos", "Redondeado"]

    def __init__(self, parent, config: AppConfig, on_apply, theme: dict):
        super().__init__(parent)
        self.config_ref = config
        self.on_apply   = on_apply
        self.t          = theme
        self.title("⚙️ Configuración avanzada")
        self.geometry("500x700")
        self.resizable(False, False)
        self.grab_set()
        self.configure(bg=theme["bg"])
        self._build()

    def _build(self):
        cfg, t = self.config_ref, self.t

        tk.Label(self, text="⚙️ Configuración avanzada",
                 font=("Segoe UI", 13, "bold"), bg=t["bg"], fg=t["fg"]).pack(pady=(18, 8))

        self.mode_var = tk.StringVar(value=cfg.content_mode)
        self.fill_var = tk.StringVar(value=cfg.fill_color)
        self.back_var = tk.StringVar(value=cfg.back_color)
        self.style_var = tk.StringVar(value=cfg.qr_style)
        self.size_var = tk.StringVar(value=cfg.size_name)
        self.corr_var = tk.StringVar(value=cfg.correction_name)
        self.logo_var = tk.BooleanVar(value=cfg.include_logo)
        self.logo_path_var = tk.StringVar(value=cfg.logo_path)
        self.barcode_format_var = tk.StringVar(value=cfg.barcode_format)
        self.barcode_width_var = tk.StringVar(value=cfg.barcode_width_name)
        self.barcode_height_var = tk.StringVar(value=cfg.barcode_height_name)
        self.barcode_show_text_var = tk.BooleanVar(value=cfg.barcode_show_text)

        def lframe(text):
            f = tk.LabelFrame(self, text=text, font=("Segoe UI", 9, "bold"),
                              padx=10, pady=8, bg=t["bg"], fg=t["fg"])
            f.pack(fill="x", padx=18, pady=5)
            return f

        frm_mode = lframe("🧭 Modo de salida")
        tk.Radiobutton(frm_mode, text="QR", variable=self.mode_var, value="QR",
                       bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"],
                       activebackground=t["bg"]).pack(side="left", padx=12)
        tk.Radiobutton(frm_mode, text="Código de barras", variable=self.mode_var, value="Barras",
                       bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"],
                       activebackground=t["bg"]).pack(side="left", padx=12)

        # — Colores —
        frm = lframe("🎨 Colores")

        def pick(var, lbl):
            c = colorchooser.askcolor(color=var.get(), title="Elige color", parent=self)[1]
            if c: var.set(c); lbl.config(bg=c)

        for label_text, var, attr in [
            ("Color QR:", self.fill_var, "fill_preview"),
            ("Color fondo:", self.back_var, "back_preview"),
        ]:
            row = tk.Frame(frm, bg=t["bg"]); row.pack(fill="x", pady=3)
            tk.Label(row, text=label_text, width=13, anchor="w", bg=t["bg"], fg=t["fg"]).pack(side="left")
            preview = tk.Label(row, bg=var.get(), width=4, relief="solid", bd=1)
            preview.pack(side="left", padx=4)
            tk.Button(row, text="Elegir…", bg=t["btn_bg"], fg=t["fg"], relief="flat",
                      command=lambda v=var, p=preview: pick(v, p)).pack(side="left")
            setattr(self, attr, preview)

        # — Estilo visual —
        frm2 = lframe("🎨 Estilo visual del QR")
        for s in self.STYLES:
            tk.Radiobutton(frm2, text=s, variable=self.style_var, value=s,
                           bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"],
                           activebackground=t["bg"]).pack(side="left", padx=10)

        # — Tamaño —
        frm3 = lframe("📐 Tamaño")
        for s in QREngine.SIZE_MAP:
            tk.Radiobutton(frm3, text=s, variable=self.size_var, value=s,
                           bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"],
                           activebackground=t["bg"]).pack(side="left", padx=8)

        # — Corrección —
        frm4 = lframe("📊 Corrección de errores")
        cb = ttk.Combobox(frm4, textvariable=self.corr_var,
                          values=list(QREngine.CORRECTION_LEVELS.keys()),
                          state="readonly", width=28)
        cb.pack(padx=4)

        # — Logo —
        frm5 = lframe("🖼 Logo central (requiere corrección H)")
        tk.Checkbutton(frm5, text="Incluir logo", variable=self.logo_var,
                       bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"],
                       activebackground=t["bg"]).pack(anchor="w")
        row_logo = tk.Frame(frm5, bg=t["bg"]); row_logo.pack(fill="x", pady=3)
        tk.Entry(row_logo, textvariable=self.logo_path_var, width=28,
                 state="readonly", bg=t["entry_bg"], fg=t["fg"]).pack(side="left", padx=(0, 4))
        tk.Button(row_logo, text="Explorar…", bg=t["btn_bg"], fg=t["fg"], relief="flat",
                  command=self._pick_logo).pack(side="left")

        frm_bar = lframe("📦 Código de barras")
        tk.Label(frm_bar, text="Formato:", width=14, anchor="w", bg=t["bg"], fg=t["fg"]).grid(row=0, column=0, sticky="w", pady=4)
        ttk.Combobox(frm_bar, textvariable=self.barcode_format_var,
                     values=QREngine.BARCODE_FORMATS, state="readonly", width=20).grid(row=0, column=1, sticky="w", pady=4)
        tk.Label(frm_bar, text="Grosor:", width=14, anchor="w", bg=t["bg"], fg=t["fg"]).grid(row=1, column=0, sticky="w", pady=4)
        ttk.Combobox(frm_bar, textvariable=self.barcode_width_var,
                     values=list(QREngine.BARCODE_WIDTH_MAP.keys()), state="readonly", width=20).grid(row=1, column=1, sticky="w", pady=4)
        tk.Label(frm_bar, text="Altura:", width=14, anchor="w", bg=t["bg"], fg=t["fg"]).grid(row=2, column=0, sticky="w", pady=4)
        ttk.Combobox(frm_bar, textvariable=self.barcode_height_var,
                     values=list(QREngine.BARCODE_HEIGHT_MAP.keys()), state="readonly", width=20).grid(row=2, column=1, sticky="w", pady=4)
        tk.Checkbutton(frm_bar, text="Mostrar texto debajo",
                       variable=self.barcode_show_text_var, bg=t["bg"], fg=t["fg"],
                       selectcolor=t["check_sel"], activebackground=t["bg"]).grid(
                           row=3, column=0, columnspan=2, sticky="w", pady=(8, 2))

        # — Presets —
        frm6 = lframe("🧩 Presets de configuración")
        row_p = tk.Frame(frm6, bg=t["bg"]); row_p.pack(fill="x")
        self.preset_name_var = tk.StringVar()
        tk.Entry(row_p, textvariable=self.preset_name_var, width=18,
                 bg=t["entry_bg"], fg=t["fg"]).pack(side="left", padx=(0, 4))
        tk.Button(row_p, text="💾 Guardar preset", bg=t["btn_bg"], fg=t["fg"],
                  relief="flat", command=self._save_preset).pack(side="left")

        # — Botones —
        btn_frm = tk.Frame(self, bg=t["bg"]); btn_frm.pack(pady=14)
        tk.Button(btn_frm, text="✅ Aplicar", bg=BTN_GREEN_L, fg="white",
                  font=("Segoe UI", 10, "bold"), relief="flat", padx=16, pady=6,
                  command=self._apply).pack(side="left", padx=8)
        tk.Button(btn_frm, text="❌ Cancelar", bg=BTN_RED_L, fg="white",
                  font=("Segoe UI", 10, "bold"), relief="flat", padx=16, pady=6,
                  command=self.destroy).pack(side="left", padx=8)

    def _pick_logo(self):
        path = filedialog.askopenfilename(
            title="Seleccionar logo",
            filetypes=[("Imágenes", "*.png *.jpg *.jpeg *.gif *.bmp"), ("Todos", "*.*")],
            parent=self)
        if path:
            self.logo_path_var.set(path)

    def _save_preset(self):
        name = self.preset_name_var.get().strip()
        if not name:
            messagebox.showwarning("Nombre requerido", "Escribe un nombre para el preset.", parent=self)
            return
        self._apply(silent=True)
        self.config_ref.save_preset(name)
        messagebox.showinfo("✅ Preset guardado", f"Preset '{name}' guardado.", parent=self)

    def _apply(self, silent=False):
        cfg = self.config_ref
        cfg.fill_color      = self.fill_var.get()
        cfg.back_color      = self.back_var.get()
        cfg.qr_style        = self.style_var.get()
        cfg.size_name       = self.size_var.get()
        cfg.correction_name = self.corr_var.get()
        cfg.include_logo    = self.logo_var.get()
        cfg.logo_path       = self.logo_path_var.get()
        cfg.content_mode    = self.mode_var.get()
        cfg.barcode_format  = self.barcode_format_var.get()
        cfg.barcode_width_name = self.barcode_width_var.get()
        cfg.barcode_height_name = self.barcode_height_var.get()
        cfg.barcode_show_text = self.barcode_show_text_var.get()
        self.on_apply()
        if not silent:
            self.destroy()


class ScanWindow(tk.Toplevel):
    """Ventana lectora de QR y códigos de barras desde imagen."""
    def __init__(self, parent, theme: dict):
        super().__init__(parent)
        self.t = theme
        self.title("📷 Lector de códigos")
        self.geometry("500x360")
        self.resizable(False, False)
        self.grab_set()
        self.configure(bg=theme["bg"])
        self._build()

    def _build(self):
        t = self.t
        tk.Label(self, text="📷 Lector / Escáner de códigos",
                 font=("Segoe UI", 13, "bold"), bg=t["bg"], fg=t["fg"]).pack(pady=(18, 6))
        tk.Label(self, text="Sube una imagen con un QR o código de barras para decodificarlo.",
                 font=("Segoe UI", 9), bg=t["bg"], fg=t["subtext"]).pack()

        frm = tk.Frame(self, bg=t["bg"]); frm.pack(pady=14)
        tk.Button(frm, text="📂 Abrir imagen…", bg=BTN_BLUE_L, fg="white",
                  font=("Segoe UI", 10, "bold"), relief="flat", padx=18, pady=8,
                  command=self._scan).pack(side="left", padx=6)
        self.drop_zone = tk.Label(
            self,
            text="Arrastra una imagen aqui para escanearla",
            font=("Segoe UI", 10, "bold"),
            bg=t["card"],
            fg=t["fg"],
            relief="solid",
            bd=1,
            padx=16,
            pady=14,
        )
        self.drop_zone.pack(fill="x", padx=20, pady=(0, 8))
        self._enable_drop_target()

        self.result_frame = tk.LabelFrame(self, text=" 🔍 Resultado ",
                                          font=("Segoe UI", 10, "bold"),
                                          bg=t["bg"], fg=t["fg"], padx=12, pady=10)
        self.result_frame.pack(fill="both", expand=True, padx=20, pady=6)

        self.result_text = tk.Text(self.result_frame, font=("Consolas", 10), height=8,
                                   wrap="word", bg=t["entry_bg"], fg=t["fg"],
                                   insertbackground=t["fg"], relief="flat", bd=0)
        self.result_text.pack(fill="both", expand=True)
        self.result_text.insert("end", "Aquí aparecerá el contenido detectado…")
        self.result_text.config(state="disabled")

        if not PYZBAR_OK:
            self.result_text.config(state="normal")
            self.result_text.delete("1.0", "end")
            self.result_text.insert("end",
                "⚠️ pyzbar no está instalado.\n\n"
                "Instala con:\n  pip install pyzbar\n\n"
                "En Windows también necesitas:\n  pip install python-opencv")
            self.result_text.config(state="disabled")

    def _scan(self):
        path = filedialog.askopenfilename(
            title="Seleccionar imagen con código",
            filetypes=[("Imágenes", "*.png *.jpg *.jpeg *.bmp *.gif"), ("Todos", "*.*")],
            parent=self)
        if not path:
            return
        self._scan_path(path)

    def _enable_drop_target(self):
        if not (TKDND_OK and hasattr(self.drop_zone, "drop_target_register")):
            self.drop_zone.config(text="Instala tkinterdnd2 para activar arrastrar y soltar.")
            return
        try:
            self.drop_zone.drop_target_register(DND_FILES)
            self.drop_zone.dnd_bind("<<Drop>>", self._on_drop)
        except Exception:
            self.drop_zone.config(text="No se pudo activar arrastrar y soltar en esta sesion.")

    def _extract_drop_path(self, data: str) -> str:
        try:
            items = self.tk.splitlist(data)
        except Exception:
            items = [data]
        for item in items:
            path = item.strip().strip('"')
            if os.path.isfile(path):
                return path
        return ""

    def _render_results(self, results: list[dict]):
        self.result_text.config(state="normal")
        self.result_text.delete("1.0", "end")
        if results:
            for i, r in enumerate(results, 1):
                self.result_text.insert("end", f"Código #{i} [{r['type']}]:\n{r['text']}\n\n")
        else:
            self.result_text.insert("end", "❌ No se encontraron códigos legibles en la imagen.\n\n"
                                           "Asegúrate de que la imagen sea clara y esté bien enfocada.")
        self.result_text.config(state="disabled")

    def _scan_path(self, path: str):
        self._render_results(QREngine.scan_image(path))

    def _on_drop(self, event):
        path = self._extract_drop_path(event.data)
        if not path:
            messagebox.showwarning("Archivo no valido", "Suelta una sola imagen compatible.", parent=self)
            return
        self._scan_path(path)


class FormBuilderWindow(tk.Toplevel):
    """Formularios inteligentes: WiFi, Email, vCard."""
    def __init__(self, parent, on_result, theme: dict):
        super().__init__(parent)
        self.on_result = on_result
        self.t         = theme
        self.title("🧩 Constructor de QR inteligente")
        self.geometry("480x460")
        self.resizable(False, False)
        self.grab_set()
        self.configure(bg=theme["bg"])
        self._build()

    def _build(self):
        t = self.t
        tk.Label(self, text="🧩 Constructor de QR inteligente",
                 font=("Segoe UI", 13, "bold"), bg=t["bg"], fg=t["fg"]).pack(pady=(14, 4))
        tk.Label(self, text="Selecciona el tipo y completa el formulario",
                 font=("Segoe UI", 9), bg=t["bg"], fg=t["subtext"]).pack()

        type_frm = tk.Frame(self, bg=t["bg"]); type_frm.pack(pady=8)
        self.form_type = tk.StringVar(value="WiFi")
        for tp in ["WiFi", "Email", "vCard"]:
            tk.Radiobutton(type_frm, text=tp, variable=self.form_type, value=tp,
                           bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"],
                           activebackground=t["bg"], font=("Segoe UI", 10, "bold"),
                           command=self._switch_form).pack(side="left", padx=12)

        self.form_container = tk.Frame(self, bg=t["bg"])
        self.form_container.pack(fill="both", expand=True, padx=20, pady=4)

        btn_frm = tk.Frame(self, bg=t["bg"]); btn_frm.pack(pady=12)
        tk.Button(btn_frm, text="⚡ Generar con este QR", bg=BTN_GREEN_L, fg="white",
                  font=("Segoe UI", 10, "bold"), relief="flat", padx=18, pady=7,
                  command=self._generate).pack(side="left", padx=6)
        tk.Button(btn_frm, text="Cancelar", bg=BTN_GREY_L, fg="white",
                  font=("Segoe UI", 10), relief="flat", padx=14, pady=7,
                  command=self.destroy).pack(side="left", padx=6)

        self._switch_form()

    def _entry_row(self, parent, label, var, show=""):
        row = tk.Frame(parent, bg=self.t["bg"]); row.pack(fill="x", pady=4)
        tk.Label(row, text=label, width=16, anchor="w",
                 font=("Segoe UI", 9), bg=self.t["bg"], fg=self.t["fg"]).pack(side="left")
        e = tk.Entry(row, textvariable=var, font=("Segoe UI", 10),
                     bg=self.t["entry_bg"], fg=self.t["fg"],
                     insertbackground=self.t["fg"], relief="solid", bd=1, show=show)
        e.pack(side="left", fill="x", expand=True)
        return e

    def _switch_form(self):
        for w in self.form_container.winfo_children():
            w.destroy()
        tp = self.form_type.get()
        t  = self.t

        if tp == "WiFi":
            self.wifi_ssid     = tk.StringVar()
            self.wifi_pass     = tk.StringVar()
            self.wifi_sec      = tk.StringVar(value="WPA")
            self.wifi_hidden   = tk.BooleanVar()
            tk.Label(self.form_container, text="📶 Configuración WiFi",
                     font=("Segoe UI", 11, "bold"), bg=t["bg"], fg=t["fg"]).pack(anchor="w", pady=(6,2))
            self._entry_row(self.form_container, "Nombre red (SSID):", self.wifi_ssid)
            self._entry_row(self.form_container, "Contraseña:", self.wifi_pass, show="•")
            row_sec = tk.Frame(self.form_container, bg=t["bg"]); row_sec.pack(fill="x", pady=4)
            tk.Label(row_sec, text="Seguridad:", width=16, anchor="w",
                     font=("Segoe UI", 9), bg=t["bg"], fg=t["fg"]).pack(side="left")
            for sec in ["WPA", "WEP", "nopass"]:
                tk.Radiobutton(row_sec, text=sec, variable=self.wifi_sec, value=sec,
                               bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"],
                               activebackground=t["bg"]).pack(side="left", padx=6)
            tk.Checkbutton(self.form_container, text="Red oculta (hidden)",
                           variable=self.wifi_hidden, bg=t["bg"], fg=t["fg"],
                           selectcolor=t["check_sel"], activebackground=t["bg"]).pack(anchor="w", pady=4)

        elif tp == "Email":
            self.email_to      = tk.StringVar()
            self.email_subject = tk.StringVar()
            self.email_body    = tk.StringVar()
            tk.Label(self.form_container, text="✉️ Configuración Email",
                     font=("Segoe UI", 11, "bold"), bg=t["bg"], fg=t["fg"]).pack(anchor="w", pady=(6,2))
            self._entry_row(self.form_container, "Para (email):", self.email_to)
            self._entry_row(self.form_container, "Asunto:", self.email_subject)
            self._entry_row(self.form_container, "Mensaje:", self.email_body)

        elif tp == "vCard":
            self.vc_name   = tk.StringVar()
            self.vc_phone  = tk.StringVar()
            self.vc_email  = tk.StringVar()
            self.vc_org    = tk.StringVar()
            self.vc_url    = tk.StringVar()
            tk.Label(self.form_container, text="👤 Configuración vCard (Contacto)",
                     font=("Segoe UI", 11, "bold"), bg=t["bg"], fg=t["fg"]).pack(anchor="w", pady=(6,2))
            self._entry_row(self.form_container, "Nombre completo:", self.vc_name)
            self._entry_row(self.form_container, "Teléfono:", self.vc_phone)
            self._entry_row(self.form_container, "Email:", self.vc_email)
            self._entry_row(self.form_container, "Organización:", self.vc_org)
            self._entry_row(self.form_container, "Sitio web:", self.vc_url)

    def _generate(self):
        tp = self.form_type.get()
        try:
            if tp == "WiFi":
                text = QREngine.build_wifi(
                    self.wifi_ssid.get(), self.wifi_pass.get(),
                    self.wifi_sec.get(), self.wifi_hidden.get())
                if not self.wifi_ssid.get():
                    raise ValueError("El nombre de la red (SSID) es requerido.")
            elif tp == "Email":
                if not self.email_to.get():
                    raise ValueError("El email destinatario es requerido.")
                text = QREngine.build_email(
                    self.email_to.get(), self.email_subject.get(), self.email_body.get())
            elif tp == "vCard":
                if not self.vc_name.get():
                    raise ValueError("El nombre es requerido.")
                text = QREngine.build_vcard(
                    self.vc_name.get(), self.vc_phone.get(),
                    self.vc_email.get(), self.vc_org.get(), self.vc_url.get())
            self.on_result(text)
            self.destroy()
        except ValueError as e:
            messagebox.showwarning("Campo requerido", str(e), parent=self)


class StatsWindow(tk.Toplevel):
    """Estadísticas del historial."""
    def __init__(self, parent, history: list, theme: dict):
        super().__init__(parent)
        self.t = theme
        self.title("📊 Estadísticas")
        self.geometry("560x500")
        self.resizable(False, False)
        self.grab_set()
        self.configure(bg=theme["bg"])
        self._build(history)

    def _build(self, history):
        t = self.t
        tk.Label(self, text="📊 Estadísticas del historial",
                 font=("Segoe UI", 13, "bold"), bg=t["bg"], fg=t["fg"]).pack(pady=(18, 12))

        total = len(history)
        tipos = Counter(entry["type"] for entry in history)
        parsed_dates = []
        for entry in history:
            try:
                parsed_dates.append(datetime.strptime(entry["timestamp"], "%d/%m/%Y %H:%M"))
            except Exception:
                continue
        last = history[0]["timestamp"] if history else "—"
        today = datetime.now().date()
        recent_days = [today - timedelta(days=offset) for offset in range(6, -1, -1)]
        by_day = Counter(item.date() for item in parsed_dates)
        today_count = by_day.get(today, 0)
        last_7_days_total = sum(by_day.get(day, 0) for day in recent_days)
        top_type = tipos.most_common(1)[0][0] if tipos else "—"

        frm = tk.Frame(self, bg=t["bg"], padx=28)
        frm.pack(fill="both", expand=True)

        def row(label, value, col=t["fg"]):
            r = tk.Frame(frm, bg=t["bg"]); r.pack(fill="x", pady=5)
            tk.Label(r, text=label, font=("Segoe UI", 10), bg=t["bg"],
                     fg=t["subtext"], width=22, anchor="w").pack(side="left")
            tk.Label(r, text=str(value), font=("Segoe UI", 10, "bold"),
                     bg=t["bg"], fg=col).pack(side="left")

        row("Total de códigos:", total, t["blue"])
        row("Última actividad:", last)
        row("Generados hoy:", today_count, t["green"])
        row("Últimos 7 días:", last_7_days_total, t["purple"])
        row("Tipo más usado:", top_type, t["yellow"])

        tk.Label(frm, text="Tipos más usados:", font=("Segoe UI", 10, "bold"),
                 bg=t["bg"], fg=t["subtext"]).pack(anchor="w", pady=(14, 4))
        for tipo, count in sorted(tipos.items(), key=lambda x: -x[1]):
            bar_len = max(18, int(count / max(total, 1) * 240))
            r2 = tk.Frame(frm, bg=t["bg"]); r2.pack(fill="x", pady=2)
            tk.Label(r2, text=f"  {tipo}", width=18, anchor="w",
                     font=("Segoe UI", 9), bg=t["bg"], fg=t["fg"]).pack(side="left")
            bar = tk.Frame(r2, bg=t["blue"], height=12, width=bar_len)
            bar.pack(side="left", padx=4)
            tk.Label(r2, text=str(count), font=("Segoe UI", 9, "bold"),
                     bg=t["bg"], fg=t["fg"]).pack(side="left")

        tk.Label(frm, text="Actividad reciente:", font=("Segoe UI", 10, "bold"),
                 bg=t["bg"], fg=t["subtext"]).pack(anchor="w", pady=(16, 4))
        for day in recent_days:
            count = by_day.get(day, 0)
            bar_len = max(8, count * 32) if count else 8
            row_day = tk.Frame(frm, bg=t["bg"])
            row_day.pack(fill="x", pady=2)
            tk.Label(row_day, text=day.strftime("%d/%m"), width=10, anchor="w",
                     font=("Segoe UI", 9), bg=t["bg"], fg=t["fg"]).pack(side="left")
            tk.Frame(row_day, bg=t["teal"], height=10, width=bar_len).pack(side="left", padx=6)
            tk.Label(row_day, text=str(count), font=("Segoe UI", 9, "bold"),
                     bg=t["bg"], fg=t["fg"]).pack(side="left")

        tk.Button(self, text="Cerrar", bg=BTN_GREY_L, fg="white", relief="flat",
                  padx=14, pady=5, command=self.destroy).pack(pady=18)


class AboutWindow(tk.Toplevel):
    def __init__(self, parent, theme: dict):
        super().__init__(parent)
        self.title("Acerca de")
        self.geometry("360x240")
        self.resizable(False, False)
        self.grab_set()
        t = theme
        self.configure(bg=t["bg"])
        tk.Label(self, text="🔲 Generador de Códigos Pro", font=("Segoe UI", 14, "bold"),
                 bg=t["bg"], fg=t["fg"]).pack(pady=(22, 4))
        tk.Label(self, text="Versión 4.0", font=("Segoe UI", 10),
                 bg=t["bg"], fg=t["subtext"]).pack()
        tk.Label(self, text="QR · Códigos de barras · Lectura · Formularios\nEstilos visuales · Historial · Presets · Tema oscuro",
                 font=("Segoe UI", 9), justify="center", bg=t["bg"], fg=t["fg"]).pack(pady=10)
        tk.Label(self, text="Python + tkinter + qrcode + Pillow + pyzbar",
                 font=("Segoe UI", 8), bg=t["bg"], fg=t["subtext"]).pack()
        tk.Button(self, text="Cerrar", command=self.destroy,
                  bg=BTN_GREY_L, fg="white", relief="flat", padx=14, pady=5).pack(pady=16)


# ══════════════════════════════════════════════════════════════
#  UI PRINCIPAL
# ══════════════════════════════════════════════════════════════

class GeneradorQR:
    TABS = ["Generador QR", "Lector QR", "Historial", "Configuración"]
    TAB_META = {
        "Generador QR": "Crea códigos QR y de barras personalizados",
        "Lector QR": "Lee QR y códigos de barras desde imágenes",
        "Historial": "Revisa tus códigos guardados",
        "Configuración": "Ajusta la experiencia de la app",
    }

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Generador de Códigos Pro")
        self.screen_width = self.root.winfo_screenwidth()
        self.screen_height = self.root.winfo_screenheight()
        usable_w = max(self.screen_width - 80, 720)
        usable_h = max(self.screen_height - 120, 520)
        initial_w = min(max(int(self.screen_width * 0.90), 960), usable_w)
        initial_h = min(max(int(self.screen_height * 0.88), 700), usable_h)
        min_w = min(max(int(initial_w * 0.72), 760), initial_w)
        min_h = min(max(int(initial_h * 0.72), 580), initial_h)
        pos_x = max((self.screen_width - initial_w) // 2, 0)
        pos_y = max((self.screen_height - initial_h) // 3, 0)
        self.root.geometry(f"{initial_w}x{initial_h}+{pos_x}+{pos_y}")
        self.root.minsize(min_w, min_h)
        self.root.resizable(True, True)
        if self.screen_width >= 1440 and self.screen_height >= 900:
            try:
                self.root.state("zoomed")
            except Exception:
                pass

        self.cfg = AppConfig()
        self.current_qr_img: Image.Image | None = None
        self.theme = DARK if self.cfg.dark_theme else LIGHT
        self.is_fullscreen = False
        self._last_layout_mode = None
        self._card_refs = []

        self.var_border = tk.BooleanVar(value=self.cfg.show_border)
        self.var_invert = tk.BooleanVar(value=self.cfg.invert)
        self.var_dark_theme = tk.BooleanVar(value=self.cfg.dark_theme)
        self.mode_var = tk.StringVar(value=self.cfg.content_mode)
        self.barcode_format_var = tk.StringVar(value=self.cfg.barcode_format)
        self.barcode_width_var = tk.StringVar(value=self.cfg.barcode_width_name)
        self.barcode_height_var = tk.StringVar(value=self.cfg.barcode_height_name)
        self.barcode_show_text_var = tk.BooleanVar(value=self.cfg.barcode_show_text)
        self.current_output_name = "codigo_qr"
        self.current_output_label = "QR"
        self._syncing_controls = False
        self._auto_preview_job = None
        self._feedback_state = "neutral"
        self._feedback_default = "La vista previa se actualiza sola mientras escribes."

        self._build_menu()
        self._build_ui()
        self._apply_theme()
        self.root.bind("<Configure>", self._on_root_resize)
        self.root.bind("<Control-n>", lambda e: self.limpiar())
        self.root.bind("<Control-s>", lambda e: self.guardar_qr())
        self.root.bind("<F11>", lambda e: self._toggle_fullscreen())
        self.root.bind("<Escape>", lambda e: self._exit_fullscreen())
        self.root.protocol("WM_DELETE_WINDOW", self._confirm_exit)
        self._restore_last_session()

    def _build_menu(self):
        menubar = tk.Menu(self.root)

        m_arch = tk.Menu(menubar, tearoff=0)
        m_arch.add_command(label="Nuevo", accelerator="Ctrl+N", command=self.limpiar)
        m_arch.add_command(label="Guardar imagen (PNG)...", accelerator="Ctrl+S", command=self.guardar_qr)
        m_arch.add_command(label="Exportar JPG...", command=lambda: self.guardar_qr(fmt="jpg"))
        m_arch.add_command(label="Exportar PDF...", command=self.exportar_pdf)
        m_arch.add_separator()
        m_arch.add_command(label="Pantalla completa", accelerator="F11", command=self._toggle_fullscreen)
        m_arch.add_separator()
        m_arch.add_command(label="Salir", accelerator="Alt+F4", command=self._confirm_exit)
        menubar.add_cascade(label="Archivo", menu=m_arch)

        m_edit = tk.Menu(menubar, tearoff=0)
        m_edit.add_command(label="Copiar texto", command=self._copy_text)
        m_edit.add_command(label="Pegar", command=self._paste_text)
        m_edit.add_separator()
        m_edit.add_command(label="Constructor QR inteligente...", command=self._open_form_builder)
        menubar.add_cascade(label="Editar", menu=m_edit)

        m_opt = tk.Menu(menubar, tearoff=0)
        m_color = tk.Menu(m_opt, tearoff=0)
        for name, hx in [("Negro", "#000000"), ("Azul", "#1565C0"), ("Rojo", "#C62828"),
                         ("Verde", "#1B5E20"), ("Morado", "#4A148C"), ("Naranja", "#E65100")]:
            m_color.add_command(label=name, command=lambda c=hx: self._quick_color(c))
        m_opt.add_cascade(label="Color rápido", menu=m_color)
        self.m_presets = tk.Menu(m_opt, tearoff=0)
        m_opt.add_cascade(label="Presets", menu=self.m_presets)
        self._rebuild_presets_menu()
        m_opt.add_separator()
        m_opt.add_checkbutton(label="Mostrar borde", variable=self.var_border, command=self._toggle_border)
        m_opt.add_checkbutton(label="Invertir colores", variable=self.var_invert, command=self._toggle_invert)
        m_opt.add_checkbutton(label="Tema oscuro", variable=self.var_dark_theme, command=self._toggle_theme)
        m_opt.add_separator()
        m_opt.add_command(label="Configuración avanzada...", command=self._open_options)
        menubar.add_cascade(label="Opciones", menu=m_opt)

        m_ver = tk.Menu(menubar, tearoff=0)
        m_ver.add_command(label="Generador QR", command=lambda: self._switch_page("Generador QR"))
        m_ver.add_command(label="Lector QR", command=lambda: self._switch_page("Lector QR"))
        m_ver.add_command(label="Historial", command=lambda: self._switch_page("Historial"))
        m_ver.add_command(label="Configuración", command=lambda: self._switch_page("Configuración"))
        menubar.add_cascade(label="Ver", menu=m_ver)

        m_help = tk.Menu(menubar, tearoff=0)
        m_help.add_command(label="Instrucciones", command=self._show_instructions)
        m_help.add_command(label="Acerca de...", command=lambda: AboutWindow(self.root, self.theme))
        menubar.add_cascade(label="Ayuda", menu=m_help)

        self.root.config(menu=menubar)

    def _build_ui(self):
        self.root.grid_rowconfigure(0, weight=1)
        self.root.grid_columnconfigure(1, weight=1)

        self.sidebar = tk.Frame(self.root, width=280)
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.grid_propagate(False)
        self.sidebar.grid_rowconfigure(3, weight=1)

        self.main_shell = tk.Frame(self.root)
        self.main_shell.grid(row=0, column=1, sticky="nsew")
        self.main_shell.grid_rowconfigure(1, weight=1)
        self.main_shell.grid_columnconfigure(0, weight=1)

        self.pages: dict[str, tk.Frame] = {}
        self._nav_btns: dict[str, tk.Button] = {}
        self.active_page = tk.StringVar(value=self.TABS[0])
        self._sidebar_nav_buttons = {}

        self._build_sidebar()
        self._build_topbar()

        self.content_shell = tk.Frame(self.main_shell)
        self.content_shell.grid(row=1, column=0, sticky="nsew", padx=24, pady=(0, 24))
        self.content_shell.grid_rowconfigure(0, weight=1)
        self.content_shell.grid_columnconfigure(0, weight=1)

        self.content_canvas = tk.Canvas(self.content_shell, highlightthickness=0, borderwidth=0)
        self.content_canvas.grid(row=0, column=0, sticky="nsew")
        self.content_scrollbar = ttk.Scrollbar(
            self.content_shell, orient="vertical", command=self.content_canvas.yview
        )
        self.content_scrollbar.grid(row=0, column=1, sticky="ns", padx=(12, 0))
        self.content_canvas.configure(yscrollcommand=self.content_scrollbar.set)

        self.content = tk.Frame(self.content_canvas)
        self.content.grid_rowconfigure(0, weight=1)
        self.content.grid_columnconfigure(0, weight=1)
        self.content_window = self.content_canvas.create_window((0, 0), window=self.content, anchor="nw")
        self.content.bind("<Configure>", self._refresh_content_scrollregion)
        self.content_canvas.bind("<Configure>", self._sync_content_canvas_width)
        self.content_canvas.bind("<MouseWheel>", self._on_content_mousewheel)

        self._build_page_generator()
        self._build_page_scanner()
        self._build_page_history()
        self._build_page_config()
        self._build_context_menu()
        self._switch_page(self.TABS[0])

    def _build_sidebar(self):
        self.brand_card = tk.Frame(self.sidebar, padx=20, pady=22)
        self.brand_card.grid(row=0, column=0, sticky="ew")
        self.brand_icon = tk.Label(self.brand_card, text="QR", font=("Segoe UI", 20, "bold"),
                                   width=3, pady=10)
        self.brand_icon.pack(side="left")
        brand_text = tk.Frame(self.brand_card)
        brand_text.pack(side="left", padx=14)
        self.brand_title = tk.Label(brand_text, text="QR Pro", font=("Segoe UI", 18, "bold"))
        self.brand_title.pack(anchor="w")
        self.brand_subtitle = tk.Label(brand_text, text="Panel inteligente", font=("Segoe UI", 10))
        self.brand_subtitle.pack(anchor="w", pady=(2, 0))

        nav_wrap = tk.Frame(self.sidebar, padx=14, pady=10)
        nav_wrap.grid(row=1, column=0, sticky="ew")
        self.nav_section_label = tk.Label(nav_wrap, text="NAVEGACIÓN", font=("Segoe UI", 9, "bold"))
        self.nav_section_label.pack(anchor="w", padx=8, pady=(0, 8))

        for name in self.TABS:
            desc = self.TAB_META[name]
            btn = tk.Button(
                nav_wrap,
                text=f"{name}\n{desc}",
                anchor="w",
                justify="left",
                relief="flat",
                padx=16,
                pady=14,
                font=("Segoe UI", 11, "bold"),
                command=lambda n=name: self._switch_page(n),
                cursor="hand2",
            )
            btn.pack(fill="x", pady=4)
            self._register_hover_button(btn)
            self._nav_btns[name] = btn
            self._sidebar_nav_buttons[name] = desc

        self.quick_box = tk.Frame(self.sidebar, padx=16, pady=16)
        self.quick_box.grid(row=2, column=0, sticky="ew", padx=14, pady=(8, 4))
        self.quick_title = tk.Label(self.quick_box, text="ATAJOS", font=("Segoe UI", 9, "bold"))
        self.quick_title.pack(anchor="w", pady=(0, 10))
        self._mkbtn(self.quick_box, "Generar ahora", BTN_GREEN_L, self.generar_qr, padx=12, pady=8).pack(fill="x", pady=3)
        self._mkbtn(self.quick_box, "Leer imagen", BTN_BLUE_L, self._scan_inline, padx=12, pady=8).pack(fill="x", pady=3)
        self._mkbtn(self.quick_box, "Constructor", BTN_PURPLE_L, self._open_form_builder, padx=12, pady=8).pack(fill="x", pady=3)

        self.side_footer = tk.Frame(self.sidebar, padx=18, pady=18)
        self.side_footer.grid(row=4, column=0, sticky="sew")
        self.side_footer.grid_columnconfigure(0, weight=1)
        self.footer_hint = tk.Label(
            self.side_footer,
            text="F11 para pantalla completa\nEsc para salir",
            justify="left",
            font=("Segoe UI", 9),
        )
        self.footer_hint.grid(row=0, column=0, sticky="w")
        self._layout_sidebar_text()

    def _layout_sidebar_text(self, sidebar_width: int | None = None):
        if sidebar_width is None:
            try:
                sidebar_width = int(self.sidebar.cget("width"))
            except Exception:
                sidebar_width = 240

        sidebar_width = max(sidebar_width, 220)
        button_wrap = max(sidebar_width - 60, 150)
        footer_wrap = max(sidebar_width - 36, 160)

        for btn in self._nav_btns.values():
            btn.config(wraplength=button_wrap)

        self.footer_hint.config(wraplength=footer_wrap)

    def _build_topbar(self):
        self.topbar = tk.Frame(self.main_shell)
        self.topbar.grid(row=0, column=0, sticky="ew", padx=24, pady=24)
        self.topbar.grid_columnconfigure(0, weight=1)
        self.topbar.grid_rowconfigure(0, weight=1)

        title_wrap = tk.Frame(self.topbar)
        title_wrap.grid(row=0, column=0, sticky="w")
        self.page_title = tk.Label(title_wrap, text="", font=("Segoe UI", 24, "bold"))
        self.page_title.pack(anchor="w")
        self.page_subtitle = tk.Label(title_wrap, text="", font=("Segoe UI", 10))
        self.page_subtitle.pack(anchor="w", pady=(4, 0))
        self.topbar_actions = tk.Frame(self.topbar)
        self.topbar_actions.grid(row=0, column=1, sticky="e")
        self.fullscreen_btn = self._mkbtn(self.topbar_actions, "Pantalla completa", BTN_BLUE_L, self._toggle_fullscreen, padx=16, pady=9)
        self.fullscreen_btn.grid(row=0, column=0, sticky="ew")
        self.options_btn = self._mkbtn(self.topbar_actions, "Opciones", BTN_PURPLE_L, self._open_options, padx=16, pady=9)
        self.options_btn.grid(row=0, column=1, sticky="ew", padx=(10, 0))
        self.topbar_action_buttons = [self.fullscreen_btn, self.options_btn]

    def _build_context_menu(self):
        self.context_menu = tk.Menu(self.root, tearoff=0)
        self.context_menu.add_command(label="Generar código", command=self.generar_qr)
        self.context_menu.add_command(label="Leer código desde imagen", command=self._scan_inline)
        self.context_menu.add_command(label="Guardar PNG", command=self.guardar_qr)
        self.context_menu.add_command(label="Exportar PDF", command=self.exportar_pdf)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="Limpiar", command=self.limpiar)
        self.root.bind("<Button-3>", self._show_context_menu)

    def _create_page_base(self, name: str):
        page = tk.Frame(self.content)
        page.grid(row=0, column=0, sticky="nsew")
        page.grid_rowconfigure(0, weight=0)
        page.grid_columnconfigure(0, weight=1)
        self.pages[name] = page
        return page

    def _refresh_content_scrollregion(self, event=None):
        if hasattr(self, "content_canvas"):
            self.content_canvas.configure(scrollregion=self.content_canvas.bbox("all"))

    def _sync_content_canvas_width(self, event):
        if hasattr(self, "content_window"):
            self.content_canvas.itemconfigure(self.content_window, width=event.width)
        self._refresh_content_scrollregion()

    def _on_content_mousewheel(self, event):
        if not hasattr(self, "content_canvas"):
            return
        step = -int(event.delta / 120) if event.delta else 0
        if step:
            self.content_canvas.yview_scroll(step, "units")

    def _card(self, parent, title, subtitle="", pad=18):
        outer = tk.Frame(parent, padx=pad, pady=pad, highlightthickness=1)
        header = tk.Frame(outer)
        header.pack(fill="x", pady=(0, 12))
        title_lbl = tk.Label(header, text=title, font=("Segoe UI", 13, "bold"))
        title_lbl.pack(anchor="w")
        subtitle_lbl = tk.Label(header, text=subtitle, font=("Segoe UI", 9), wraplength=500, justify="left")
        subtitle_lbl.pack(anchor="w", pady=(4, 0))
        body = tk.Frame(outer)
        body.pack(fill="both", expand=True)
        self._card_refs.append((outer, header, body, title_lbl, subtitle_lbl))
        return outer, body, subtitle_lbl

    def _build_page_generator(self):
        page = self._create_page_base("Generador QR")
        page.grid_rowconfigure(1, weight=1)
        page.grid_rowconfigure(2, weight=0)
        page.grid_columnconfigure(0, weight=1)

        self.hero_card, hero_body, _ = self._card(
            page,
            "Genera QR y barras con diseño moderno",
            "Crea enlaces, WiFi, emails, contactos y también códigos de barras listos para usar.",
            pad=22,
        )
        self.hero_card.grid(row=0, column=0, sticky="ew", pady=(0, 18))
        hero_body.grid_columnconfigure(0, weight=1)
        hero_body.grid_columnconfigure(1, weight=1)

        self.hero_left = tk.Frame(hero_body)
        self.hero_left.grid(row=0, column=0, sticky="ew", padx=(0, 10))
        self.hero_stats = tk.Label(self.hero_left, text="Listo para generar", font=("Segoe UI", 11, "bold"))
        self.hero_stats.pack(anchor="w")
        self.hero_desc = tk.Label(
            self.hero_left,
            text="Escribe tu contenido y la vista previa se actualiza automáticamente.",
            font=("Segoe UI", 10),
            justify="left",
            wraplength=460,
        )
        self.hero_desc.pack(anchor="w", pady=(8, 0))

        self.hero_actions = tk.Frame(hero_body)
        self.hero_actions.grid(row=0, column=1, sticky="e")
        self.hero_generate_btn = self._mkbtn(self.hero_actions, "Generar QR", BTN_GREEN_L, self.generar_qr, padx=18, pady=10)
        self.hero_builder_btn = self._mkbtn(self.hero_actions, "Constructor", BTN_PURPLE_L, self._open_form_builder, padx=18, pady=10)
        self.btn_guardar = self._mkbtn(self.hero_actions, "Guardar imagen", BTN_BLUE_L, self.guardar_qr, state="disabled", padx=18, pady=10)
        self.btn_exportar_pdf = self._mkbtn(self.hero_actions, "Exportar PDF", BTN_TEAL_L, self.exportar_pdf, state="disabled", padx=18, pady=10)
        self.hero_action_buttons = [self.hero_generate_btn, self.hero_builder_btn, self.btn_guardar, self.btn_exportar_pdf]

        self.generator_grid = tk.Frame(page)
        self.generator_grid.grid(row=1, column=0, sticky="nsew")
        self.generator_grid.grid_rowconfigure(0, weight=1)
        self.generator_grid.grid_rowconfigure(1, weight=0)
        self.generator_grid.grid_rowconfigure(2, weight=0)
        self.generator_grid.grid_columnconfigure(0, weight=1)
        self.generator_grid.grid_columnconfigure(1, weight=1)

        left_card, left_body, _ = self._card(
            self.generator_grid,
            "Contenido y controles",
            "El contenido y las acciones principales se adaptan automáticamente al ancho disponible.",
        )
        self.generator_left_card = left_card
        left_card.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        left_body.grid_columnconfigure(0, weight=1)

        input_box = tk.Frame(left_body)
        input_box.pack(fill="x", pady=(0, 14))
        self.input_title = tk.Label(input_box, text="Contenido del QR", font=("Segoe UI", 11, "bold"))
        self.input_title.pack(anchor="w")
        self.input_hint = tk.Label(input_box, text="URL, texto, WiFi, email, teléfono o vCard", font=("Segoe UI", 9))
        self.input_hint.pack(anchor="w", pady=(4, 10))

        self.mode_row = tk.Frame(left_body)
        self.mode_row.pack(fill="x", pady=(0, 12))
        self.mode_label = tk.Label(self.mode_row, text="Tipo de código", font=("Segoe UI", 10, "bold"))
        self.mode_qr_btn = tk.Radiobutton(
            self.mode_row, text="QR", variable=self.mode_var, value="QR",
            command=lambda: self._set_content_mode("QR")
        )
        self.mode_barcode_btn = tk.Radiobutton(
            self.mode_row, text="Código de barras", variable=self.mode_var, value="Barras",
            command=lambda: self._set_content_mode("Barras")
        )

        self.barcode_inline_row = tk.Frame(left_body)
        self.barcode_inline_row.pack(fill="x", pady=(0, 12))
        self.barcode_inline_label = tk.Label(
            self.barcode_inline_row, text="Formato de barras:", font=("Segoe UI", 9, "bold")
        )
        self.barcode_format_cb = ttk.Combobox(
            self.barcode_inline_row,
            textvariable=self.barcode_format_var,
            values=QREngine.BARCODE_FORMATS,
            state="readonly",
            width=16,
        )
        self.barcode_format_cb.bind("<<ComboboxSelected>>", lambda e: self._on_barcode_format_change())
        self.barcode_inline_hint = tk.Label(
            self.barcode_inline_row,
            text="EAN/UPC calculan el dígito verificador si falta.",
            font=("Segoe UI", 8),
        )

        self.entrada_texto = tk.Entry(input_box, font=("Segoe UI", 13), relief="flat", bd=0)
        self.entrada_texto.pack(fill="x", ipady=10)
        self.entrada_texto.bind("<KeyRelease>", self._on_text_change)
        self.live_feedback_lbl = tk.Label(
            input_box,
            text=self._feedback_default,
            font=("Segoe UI", 9),
            justify="left",
            wraplength=440,
        )
        self.live_feedback_lbl.pack(anchor="w", pady=(10, 0))

        type_row = tk.Frame(left_body)
        type_row.pack(fill="x", pady=(0, 14))
        self.type_lbl = tk.Label(type_row, text="Tipo: —", font=("Segoe UI", 10, "italic"))
        self.type_lbl.pack(side="left")
        self._mkbtn(type_row, "Pegar", BTN_GREY_L, self._paste_text, padx=12, pady=7).pack(side="right", padx=(8, 0))
        self._mkbtn(type_row, "Copiar", BTN_GREY_L, self._copy_text, padx=12, pady=7).pack(side="right")

        action_row = tk.Frame(left_body)
        action_row.pack(fill="x", pady=(0, 16))
        self.btn_generar = self._mkbtn(action_row, "Generar QR", BTN_GREEN_L, self.generar_qr, padx=16, pady=9)
        self.btn_generar.pack(side="left", padx=(0, 8))
        self.btn_limpiar = self._mkbtn(action_row, "Limpiar", BTN_RED_L, self.limpiar, padx=16, pady=9)
        self.btn_limpiar.pack(side="left", padx=(0, 8))
        self.btn_opciones = self._mkbtn(action_row, "Opciones", BTN_PURPLE_L, self._open_options, padx=16, pady=9)
        self.btn_opciones.pack(side="left")

        type_row.destroy()
        action_row.destroy()

        self.type_row = tk.Frame(left_body)
        self.type_row.pack(fill="x", pady=(0, 14))
        self.type_row.grid_columnconfigure(0, weight=1)
        self.type_info_wrap = tk.Frame(self.type_row)
        self.type_info_wrap.grid(row=0, column=0, sticky="w")
        self.type_lbl = tk.Label(self.type_info_wrap, text="Tipo: â€”", font=("Segoe UI", 10, "italic"))
        self.type_lbl.pack(anchor="w")
        self.type_action_wrap = tk.Frame(self.type_row)
        self.type_action_wrap.grid(row=0, column=1, sticky="e")
        self.copy_btn = self._mkbtn(self.type_action_wrap, "Copiar", BTN_GREY_L, self._copy_text, padx=12, pady=7)
        self.paste_btn = self._mkbtn(self.type_action_wrap, "Pegar", BTN_GREY_L, self._paste_text, padx=12, pady=7)
        self.type_action_buttons = [self.copy_btn, self.paste_btn]

        self.action_row = tk.Frame(left_body)
        self.action_row.pack(fill="x", pady=(0, 16))
        self.btn_generar = self._mkbtn(self.action_row, "Generar QR", BTN_GREEN_L, self.generar_qr, padx=16, pady=9)
        self.btn_limpiar = self._mkbtn(self.action_row, "Limpiar", BTN_RED_L, self.limpiar, padx=16, pady=9)
        self.btn_opciones = self._mkbtn(self.action_row, "Opciones", BTN_PURPLE_L, self._open_options, padx=16, pady=9)
        self.main_action_buttons = [self.btn_generar, self.btn_limpiar, self.btn_opciones]

        self.summary_card, summary_body, _ = self._card(
            self.generator_grid,
            "Configuración activa",
            "Resumen visual de los ajustes que se usarán para generar el próximo código.",
            pad=16,
        )
        self.summary_card.grid(row=1, column=0, sticky="ew", padx=(0, 10), pady=(18, 0))
        row_colors = tk.Frame(summary_body)
        row_colors.pack(fill="x", pady=(0, 10))
        tk.Label(row_colors, text="QR", font=("Segoe UI", 9, "bold")).pack(side="left")
        self.cfg_fill_preview = tk.Label(row_colors, width=3, relief="solid", bd=1)
        self.cfg_fill_preview.pack(side="left", padx=(6, 14))
        tk.Label(row_colors, text="Fondo", font=("Segoe UI", 9, "bold")).pack(side="left")
        self.cfg_back_preview = tk.Label(row_colors, width=3, relief="solid", bd=1)
        self.cfg_back_preview.pack(side="left", padx=(6, 0))

        details = tk.Frame(summary_body)
        details.pack(fill="x")
        self.cfg_mode_lbl = tk.Label(details, text="")
        self.cfg_mode_lbl.pack(anchor="w", pady=2)
        self.cfg_size_lbl = tk.Label(details, text="")
        self.cfg_size_lbl.pack(anchor="w", pady=2)
        self.cfg_style_lbl = tk.Label(details, text="")
        self.cfg_style_lbl.pack(anchor="w", pady=2)
        self.cfg_corr_lbl = tk.Label(details, text="")
        self.cfg_corr_lbl.pack(anchor="w", pady=2)
        self.cfg_barcode_lbl = tk.Label(details, text="")
        self.cfg_barcode_lbl.pack(anchor="w", pady=2)
        self.cfg_barcode_size_lbl = tk.Label(details, text="")
        self.cfg_barcode_size_lbl.pack(anchor="w", pady=2)
        self._config_detail_labels = [
            self.cfg_mode_lbl,
            self.cfg_size_lbl,
            self.cfg_style_lbl,
            self.cfg_corr_lbl,
            self.cfg_barcode_lbl,
            self.cfg_barcode_size_lbl,
        ]

        right_card, right_body, _ = self._card(
            self.generator_grid,
            "Vista previa",
            "La vista previa se adapta automáticamente al espacio disponible de la ventana.",
        )
        self.generator_right_card = right_card
        right_card.grid(row=0, column=1, rowspan=2, sticky="nsew", padx=(10, 0))
        right_body.pack_propagate(False)

        self.preview_panel = tk.Frame(right_body)
        self.preview_panel.pack(fill="both", expand=True)
        self.preview_panel.bind("<Configure>", self._refresh_preview)

        self.label_qr = tk.Label(self.preview_panel)
        self.label_qr.pack(expand=True)
        self.placeholder_lbl = tk.Label(
            self.preview_panel,
            text="El código QR aparecerá aquí\n\nEscribe un contenido y la vista previa se actualizará sola",
            font=("Segoe UI", 12),
            justify="center",
        )
        self.placeholder_lbl.place(relx=0.5, rely=0.5, anchor="center")
        self._update_mode_ui()

    def _build_page_scanner(self):
        page = self._create_page_base("Lector QR")
        page.grid_rowconfigure(1, weight=1)
        page.grid_columnconfigure(0, weight=1)

        info_card, info_body, _ = self._card(
            page,
            "Escáner desde imagen",
            "Carga o arrastra una imagen PNG, JPG, BMP o GIF para decodificar QR y códigos de barras.",
            pad=22,
        )
        info_card.grid(row=0, column=0, sticky="ew", pady=(0, 18))
        toolbar = tk.Frame(info_body)
        toolbar.pack(fill="x")
        self._mkbtn(toolbar, "Abrir imagen y escanear", BTN_BLUE_L, self._scan_inline, padx=18, pady=10).pack(side="left")
        self._mkbtn(toolbar, "Usar en generador", BTN_GREEN_L, self._use_scan_result, padx=18, pady=10).pack(side="left", padx=8)
        self.scan_drop_zone = tk.Label(
            info_body,
            text="Arrastra una imagen aquí para escanearla al instante",
            font=("Segoe UI", 10, "bold"),
            relief="solid",
            bd=1,
            padx=16,
            pady=18,
            cursor="hand2" if TKDND_OK else "arrow",
        )
        self.scan_drop_zone.pack(fill="x", pady=(14, 0))
        self._enable_drop_target(
            self.scan_drop_zone,
            self._handle_scan_drop,
            fallback_text="Instala tkinterdnd2 para activar arrastrar y soltar en el escáner.",
        )

        result_card, result_body, _ = self._card(
            page,
            "Resultado del escaneo",
            "Si hay varios códigos en la imagen, aparecerán listados aquí.",
        )
        result_card.grid(row=1, column=0, sticky="nsew")
        result_body.grid_rowconfigure(0, weight=1)
        result_body.grid_columnconfigure(0, weight=1)

        self.scan_text = tk.Text(result_body, font=("Consolas", 11), wrap="word", relief="flat", bd=0)
        self.scan_text.grid(row=0, column=0, sticky="nsew")
        self.scan_result_text = ""
        if not PYZBAR_OK:
            self.scan_text.insert("end", "pyzbar no está instalado.\n\nInstala con:\n  pip install pyzbar")
        else:
            self.scan_text.insert("end", "Abre una imagen para escanear su código...")
        self.scan_text.config(state="disabled")

    def _build_page_history(self):
        page = self._create_page_base("Historial")
        page.grid_rowconfigure(1, weight=1)
        page.grid_columnconfigure(0, weight=1)

        top_card, top_body, _ = self._card(
            page,
            "Historial reciente",
            "Revisa tus últimos códigos generados y exporta cualquiera que tenga imagen almacenada.",
            pad=22,
        )
        top_card.grid(row=0, column=0, sticky="ew", pady=(0, 18))
        tool_row = tk.Frame(top_body)
        tool_row.pack(fill="x")
        self._mkbtn(tool_row, "Guardar seleccionado", BTN_BLUE_L, self._save_history_item, padx=18, pady=9).pack(side="left")
        self._mkbtn(tool_row, "Estadísticas", BTN_TEAL_L, self._open_stats, padx=18, pady=9).pack(side="left", padx=8)
        self._mkbtn(tool_row, "Borrar historial", BTN_RED_L, self._clear_history, padx=18, pady=9).pack(side="left")

        table_card, table_body, _ = self._card(
            page,
            "Registros guardados",
            "Los elementos marcados sin imagen requieren volver a generarse para exportarlos.",
        )
        table_card.grid(row=1, column=0, sticky="nsew")
        table_body.grid_rowconfigure(0, weight=1)
        table_body.grid_columnconfigure(0, weight=1)

        cols = ("Texto / URL", "Tipo", "Fecha")
        self.hist_tree = ttk.Treeview(table_body, columns=cols, show="headings", selectmode="browse")
        for c, w in zip(cols, [540, 140, 180]):
            self.hist_tree.heading(c, text=c)
            self.hist_tree.column(c, width=w, anchor="w")
        sb = ttk.Scrollbar(table_body, orient="vertical", command=self.hist_tree.yview)
        self.hist_tree.configure(yscrollcommand=sb.set)
        self.hist_tree.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")

    def _build_page_config(self):
        page = self._create_page_base("Configuración")
        page.grid_rowconfigure(0, weight=1)
        page.grid_columnconfigure(0, weight=1)

        self.config_grid = tk.Frame(page)
        self.config_grid.grid(row=0, column=0, sticky="nsew")
        self.config_grid.grid_rowconfigure(0, weight=1)
        self.config_grid.grid_rowconfigure(1, weight=1)
        self.config_grid.grid_columnconfigure(0, weight=1)
        self.config_grid.grid_columnconfigure(1, weight=1)

        general_card, general_body, _ = self._card(
            self.config_grid,
            "Preferencias generales",
            "Activa opciones visuales y de comportamiento rápido.",
            pad=20,
        )
        self.config_general_card = general_card
        general_card.grid(row=0, column=0, sticky="nsew", padx=(0, 10))

        def pref_row(parent, text, var, cmd):
            row = tk.Frame(parent)
            row.pack(fill="x", pady=6)
            tk.Label(row, text=text, font=("Segoe UI", 10)).pack(side="left")
            tk.Checkbutton(row, variable=var, command=cmd).pack(side="right")

        mode_row = tk.Frame(general_body)
        mode_row.pack(fill="x", pady=(0, 10))
        tk.Label(mode_row, text="Modo predeterminado", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        tk.Radiobutton(mode_row, text="QR", variable=self.mode_var, value="QR",
                       command=lambda: self._set_content_mode("QR")).pack(side="left", padx=(0, 12), pady=(6, 0))
        tk.Radiobutton(mode_row, text="Código de barras", variable=self.mode_var, value="Barras",
                       command=lambda: self._set_content_mode("Barras")).pack(side="left", pady=(6, 0))

        pref_row(general_body, "Tema oscuro", self.var_dark_theme, self._toggle_theme)
        pref_row(general_body, "Mostrar borde", self.var_border, self._toggle_border)
        pref_row(general_body, "Invertir colores", self.var_invert, self._toggle_invert)

        engine_card, engine_body, _ = self._card(
            self.config_grid,
            "Ajustes del motor",
            "Cambia las opciones base tanto para QR como para códigos de barras.",
            pad=20,
        )
        self.config_engine_card = engine_card
        engine_card.grid(row=0, column=1, sticky="nsew", padx=(10, 0))

        self.corr_var_cfg = tk.StringVar(value=self.cfg.correction_name)
        tk.Label(engine_body, text="Corrección de errores", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        cb = ttk.Combobox(engine_body, textvariable=self.corr_var_cfg,
                          values=list(QREngine.CORRECTION_LEVELS.keys()), state="readonly")
        cb.pack(fill="x", pady=(6, 14))
        cb.bind("<<ComboboxSelected>>", lambda e: (setattr(self.cfg, "correction_name", self.corr_var_cfg.get()),
                                                   self._save_config_state(regenerate=self.mode_var.get() == "QR")))

        self.size_var_cfg = tk.StringVar(value=self.cfg.size_name)
        tk.Label(engine_body, text="Tamaño por defecto", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        size_row = tk.Frame(engine_body)
        size_row.pack(fill="x", pady=(6, 14))
        for s in QREngine.SIZE_MAP:
            tk.Radiobutton(size_row, text=s, variable=self.size_var_cfg, value=s,
                           command=lambda v=s: self._set_default_size(v)).pack(side="left", padx=(0, 12))

        self.style_var_cfg = tk.StringVar(value=self.cfg.qr_style)
        tk.Label(engine_body, text="Estilo visual", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        style_row = tk.Frame(engine_body)
        style_row.pack(fill="x", pady=(6, 14))
        for st in ["Clásico", "Puntos", "Redondeado"]:
            tk.Radiobutton(style_row, text=st, variable=self.style_var_cfg, value=st,
                           command=lambda v=st: self._set_default_style(v)).pack(side="left", padx=(0, 12))

        tk.Label(engine_body, text="Formato de código de barras", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        self.barcode_format_cfg = ttk.Combobox(engine_body, textvariable=self.barcode_format_var,
                                               values=QREngine.BARCODE_FORMATS, state="readonly")
        self.barcode_format_cfg.pack(fill="x", pady=(6, 14))
        self.barcode_format_cfg.bind("<<ComboboxSelected>>", lambda e: self._on_barcode_format_change())

        barcode_size_row = tk.Frame(engine_body)
        barcode_size_row.pack(fill="x", pady=(0, 12))
        tk.Label(barcode_size_row, text="Grosor", font=("Segoe UI", 10, "bold")).grid(row=0, column=0, sticky="w")
        ttk.Combobox(barcode_size_row, textvariable=self.barcode_width_var,
                     values=list(QREngine.BARCODE_WIDTH_MAP.keys()), state="readonly", width=12).grid(
                         row=1, column=0, sticky="w", pady=(6, 0))
        tk.Label(barcode_size_row, text="Altura", font=("Segoe UI", 10, "bold")).grid(row=0, column=1, sticky="w", padx=(18, 0))
        ttk.Combobox(barcode_size_row, textvariable=self.barcode_height_var,
                     values=list(QREngine.BARCODE_HEIGHT_MAP.keys()), state="readonly", width=12).grid(
                         row=1, column=1, sticky="w", padx=(18, 0), pady=(6, 0))
        self.barcode_width_var.trace_add("write", lambda *_: self._on_barcode_size_change())
        self.barcode_height_var.trace_add("write", lambda *_: self._on_barcode_size_change())

        tk.Checkbutton(engine_body, text="Mostrar texto en el código de barras",
                       variable=self.barcode_show_text_var, command=self._on_barcode_text_toggle).pack(anchor="w", pady=(2, 12))

        self._mkbtn(engine_body, "Abrir configuración avanzada", BTN_PURPLE_L, self._open_options, padx=18, pady=10).pack(anchor="w", pady=(8, 0))

    def _mkbtn(self, parent, text, color, cmd, state="normal", padx=20, pady=8):
        btn = tk.Button(parent, text=text, command=cmd, state=state,
                        font=("Segoe UI", 10, "bold"), bg=color, fg="white",
                        relief="flat", padx=padx, pady=pady, cursor="hand2",
                        activeforeground="white")
        btn._accent_source = color
        self._register_hover_button(btn)
        return btn

    def _register_hover_button(self, btn: tk.Button):
        if getattr(btn, "_hover_registered", False):
            return
        btn._hover_registered = True
        btn._hovered = False
        btn._hover_job = None
        btn.bind("<Enter>", lambda e, b=btn: self._on_button_hover(b, True), add="+")
        btn.bind("<Leave>", lambda e, b=btn: self._on_button_hover(b, False), add="+")
        btn.bind("<ButtonRelease-1>", lambda e, b=btn: self._on_button_release(b, e), add="+")

    def _on_button_release(self, btn: tk.Button, event):
        hovered = btn.winfo_containing(event.x_root, event.y_root) == btn
        self._on_button_hover(btn, hovered)

    def _on_button_hover(self, btn: tk.Button, hovered: bool):
        if not btn.winfo_exists():
            return
        if str(btn.cget("state")) == "disabled":
            hovered = False
        btn._hovered = hovered
        target = getattr(btn, "_hover_bg", btn.cget("bg")) if hovered else getattr(btn, "_base_bg", btn.cget("bg"))
        self._animate_button_bg(btn, target)

    def _animate_button_bg(self, btn: tk.Button, target: str, steps: int = 4, delay: int = 18):
        if not btn.winfo_exists():
            return
        current = btn.cget("bg")
        if not isinstance(current, str) or not current.startswith("#"):
            btn.config(bg=target, activebackground=target)
            return
        if current.lower() == target.lower():
            btn.config(bg=target, activebackground=target)
            return
        job = getattr(btn, "_hover_job", None)
        if job:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        colors = [blend_hex(current, target, idx / steps) for idx in range(1, steps + 1)]

        def step(index=0):
            if not btn.winfo_exists():
                return
            tone = colors[index]
            btn.config(bg=tone, activebackground=tone)
            if index + 1 < len(colors):
                btn._hover_job = self.root.after(delay, lambda: step(index + 1))
            else:
                btn._hover_job = None

        step()

    def _set_button_palette(self, btn: tk.Button, base: str, hover: str | None = None, fg: str = "white"):
        hover = hover or shift_hex(base, 0.14)
        btn._base_bg = base
        btn._hover_bg = hover
        btn._base_fg = fg
        current = hover if getattr(btn, "_hovered", False) else base
        btn.config(bg=current, fg=fg, activebackground=current, activeforeground=fg)

    def _schedule_preview_regeneration(self, delay_ms: int = 300):
        self._cancel_preview_regeneration()
        self._auto_preview_job = self.root.after(delay_ms, self._run_scheduled_preview)

    def _cancel_preview_regeneration(self):
        if self._auto_preview_job is not None:
            try:
                self.root.after_cancel(self._auto_preview_job)
            except Exception:
                pass
            self._auto_preview_job = None

    def _run_scheduled_preview(self):
        self._auto_preview_job = None
        self._regenerate_preview_if_possible()

    def _save_config_state(self, *, regenerate: bool = False, refresh_text: bool = False,
                           sync_controls: bool = False, rebuild_presets: bool = False):
        if sync_controls:
            self._sync_config_controls()
        if refresh_text:
            self._on_text_change(schedule_preview=False)
        self._update_config_preview()
        if regenerate:
            self._regenerate_preview_if_possible()
        if rebuild_presets:
            self._rebuild_presets_menu()
        self.cfg.save()

    def _restore_last_session(self):
        if not hasattr(self, "entrada_texto"):
            return
        if self.cfg.last_text:
            self._set_input_text(self.cfg.last_text, trigger_preview=True)
        else:
            self._set_live_feedback(self._feedback_default, "neutral")

    def _set_input_text(self, value: str, *, trigger_preview: bool = True):
        self.entrada_texto.delete(0, tk.END)
        self.entrada_texto.insert(0, value)
        self.entrada_texto.icursor(tk.END)
        self.cfg.last_text = value
        if trigger_preview:
            self._on_text_change()
        else:
            self.cfg.save()

    def _set_live_feedback(self, text: str, state: str = "neutral"):
        self._feedback_state = state
        if hasattr(self, "live_feedback_lbl"):
            self.live_feedback_lbl.config(text=text)
        if hasattr(self, "hero_desc") and self.current_qr_img is None:
            self.hero_desc.config(text=text)
        if hasattr(self, "live_feedback_lbl"):
            palette = {
                "neutral": self.theme["subtext"],
                "ok": self.theme["green"],
                "warn": self.theme["yellow"],
                "error": self.theme["red"],
                "info": self.theme["blue"],
            }
            self.live_feedback_lbl.config(fg=palette.get(state, self.theme["subtext"]))

    def _describe_live_input(self, text: str) -> tuple[str, str]:
        clean = text.strip()
        if not clean:
            return self._feedback_default, "neutral"

        if self.mode_var.get() == "Barras":
            try:
                normalized = QREngine.normalize_barcode_data(clean, self.cfg.barcode_format)
                if normalized != clean:
                    return f"Listo para {self.cfg.barcode_format}. Se normalizará como {normalized}.", "ok"
                return f"Formato válido para {self.cfg.barcode_format}. Vista previa automática lista.", "ok"
            except ValueError as exc:
                return str(exc), "error"

        dtype = QREngine.detect_type(clean)
        if dtype == "URL":
            if clean.lower().startswith("www."):
                return "Parece una URL. Añade https:// para que quede lista al escanear.", "warn"
            parsed = urlparse(clean)
            if parsed.scheme and parsed.netloc:
                return "URL detectada. La vista previa se actualiza automáticamente.", "info"
            return "La URL parece incompleta. Revisa el dominio o el protocolo.", "warn"
        if dtype == "Email":
            return "Email detectado. Puedes generar el QR directamente.", "ok"
        if dtype == "WiFi":
            if "S:" not in clean.upper():
                return "Formato WiFi incompleto: falta el nombre de la red.", "error"
            return "WiFi detectado. El QR quedará listo para conexión rápida.", "ok"
        if dtype == "Teléfono":
            digits = re.sub(r"\D", "", clean)
            if len(digits) < 7:
                return "El teléfono parece corto. Revisa el número antes de compartirlo.", "warn"
            return "Teléfono detectado. La vista previa se mantendrá actualizada.", "ok"
        if len(clean) > 220:
            return "Contenido largo detectado. El QR será más denso, pero sigue siendo válido.", "warn"
        return "Texto detectado. La vista previa se actualiza sola mientras escribes.", "neutral"

    def _enable_drop_target(self, widget, callback, fallback_text: str | None = None):
        if not (TKDND_OK and hasattr(widget, "drop_target_register")):
            if fallback_text:
                widget.config(text=fallback_text, cursor="arrow")
            return
        try:
            widget.drop_target_register(DND_FILES)
            widget.dnd_bind("<<Drop>>", callback)
        except Exception:
            if fallback_text:
                widget.config(text=fallback_text, cursor="arrow")

    def _extract_drop_path(self, data: str) -> str:
        try:
            candidates = self.root.tk.splitlist(data)
        except Exception:
            candidates = [data]
        for item in candidates:
            path = item.strip().strip('"')
            if os.path.isfile(path):
                return path
        return ""

    def _switch_page(self, name: str):
        for page in self.pages.values():
            page.grid_remove()
        self.pages[name].grid()
        if name == "Historial":
            self._refresh_history_tree()
        desc = self.TAB_META[name]
        self.page_title.config(text=name)
        self.page_subtitle.config(text=desc)
        self.active_page.set(name)
        self._update_nav_buttons()
        self._apply_responsive_layout()
        self._refresh_content_scrollregion()

    def _update_nav_buttons(self):
        active = self.active_page.get()
        t = self.theme
        for name, btn in self._nav_btns.items():
            if name == active:
                btn.config(text=f"{name}\n{self._sidebar_nav_buttons[name]}", justify="left")
                self._set_button_palette(btn, t["blue"], shift_hex(t["blue"], 0.16), "white")
            else:
                btn.config(text=f"{name}\n{self._sidebar_nav_buttons[name]}", justify="left")
                self._set_button_palette(btn, t["sidebar"], t["card2"], t["fg"])
        self._layout_sidebar_text()

    def _toggle_fullscreen(self):
        self.is_fullscreen = not self.is_fullscreen
        self.root.attributes("-fullscreen", self.is_fullscreen)
        self.fullscreen_btn.config(text="Salir pantalla completa" if self.is_fullscreen else "Pantalla completa")

    def _exit_fullscreen(self):
        if self.is_fullscreen:
            self.is_fullscreen = False
            self.root.attributes("-fullscreen", False)
            self.fullscreen_btn.config(text="Pantalla completa")

    def _on_root_resize(self, event=None):
        if event is not None and event.widget is not self.root:
            return
        self._apply_responsive_layout()
        self._refresh_preview()

    def _get_layout_mode(self, width: int) -> str:
        if width >= 1380:
            return "wide"
        if width >= 1120:
            return "medium"
        if width >= 860:
            return "compact"
        return "narrow"

    def _layout_button_group(self, frame, buttons, columns: int):
        columns = max(1, min(columns, len(buttons)))
        for btn in buttons:
            btn.grid_forget()
        for col in range(max(len(buttons), 4)):
            frame.grid_columnconfigure(col, weight=0)
        for idx, btn in enumerate(buttons):
            row = idx // columns
            col = idx % columns
            btn.grid(
                row=row,
                column=col,
                sticky="ew",
                padx=(0 if col == 0 else 10, 0),
                pady=(0 if row == 0 else 10, 0),
            )
            frame.grid_columnconfigure(col, weight=1)

    def _layout_generator_controls(self, width: int):
        controls_stacked = width < 980
        controls_single_column = width < 760

        for widget in (self.mode_label, self.mode_qr_btn, self.mode_barcode_btn):
            widget.grid_forget()
        if controls_stacked:
            self.mode_label.grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 6))
            self.mode_qr_btn.grid(row=1, column=0, sticky="w")
            self.mode_barcode_btn.grid(row=1, column=1, sticky="w", padx=(12, 0))
        else:
            self.mode_label.grid(row=0, column=0, sticky="w")
            self.mode_qr_btn.grid(row=0, column=1, sticky="w", padx=(16, 8))
            self.mode_barcode_btn.grid(row=0, column=2, sticky="w")

        for widget in (self.barcode_inline_label, self.barcode_format_cb, self.barcode_inline_hint):
            widget.grid_forget()
        self.barcode_inline_row.grid_columnconfigure(0, weight=0)
        self.barcode_inline_row.grid_columnconfigure(1, weight=1)
        self.barcode_inline_row.grid_columnconfigure(2, weight=0)
        if controls_stacked:
            self.barcode_inline_label.grid(row=0, column=0, sticky="w")
            self.barcode_format_cb.grid(row=0, column=1, sticky="ew", padx=(10, 0))
            self.barcode_inline_hint.grid(row=1, column=0, columnspan=2, sticky="w", pady=(8, 0))
        else:
            self.barcode_inline_label.grid(row=0, column=0, sticky="w")
            self.barcode_format_cb.grid(row=0, column=1, sticky="w", padx=(10, 10))
            self.barcode_inline_hint.grid(row=0, column=2, sticky="w")

        self.type_info_wrap.grid_forget()
        self.type_action_wrap.grid_forget()
        if controls_stacked:
            self.type_info_wrap.grid(row=0, column=0, columnspan=2, sticky="w")
            self.type_action_wrap.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        else:
            self.type_info_wrap.grid(row=0, column=0, sticky="w")
            self.type_action_wrap.grid(row=0, column=1, sticky="e")
        self._layout_button_group(
            self.type_action_wrap,
            self.type_action_buttons,
            1 if controls_single_column else 2,
        )

        action_cols = 1 if controls_single_column else 2 if controls_stacked else 3
        self._layout_button_group(self.action_row, self.main_action_buttons, action_cols)

    def _apply_responsive_layout(self):
        width = self.root.winfo_width()
        mode = self._get_layout_mode(width)
        if mode == self._last_layout_mode:
            self._layout_generator_controls(width)
            self._layout_dynamic_text(width)
            self._refresh_content_scrollregion()
            return
        self._last_layout_mode = mode

        outer_pad = 24 if mode in ("wide", "medium") else 16 if mode == "compact" else 12
        sidebar_width = 288 if mode == "wide" else 252 if mode == "medium" else 228 if mode == "compact" else 212

        self.sidebar.config(width=sidebar_width)
        self.topbar.grid_configure(padx=outer_pad, pady=(outer_pad, outer_pad))
        self.content_shell.grid_configure(padx=outer_pad, pady=(0, outer_pad))

        if mode == "narrow":
            self.topbar_actions.grid_configure(row=1, column=0, columnspan=2, sticky="ew", pady=(14, 0))
            self.hero_actions.grid_configure(row=1, column=0, columnspan=2, sticky="ew", pady=(18, 0))
            self.generator_left_card.grid_configure(row=0, column=0, padx=0, pady=(0, 16))
            self.generator_right_card.grid_configure(row=1, column=0, rowspan=1, padx=0, pady=(0, 16))
            self.summary_card.grid_configure(row=2, column=0, padx=0, pady=(0, 16))
            self.generator_grid.grid_rowconfigure(0, weight=0)
            self.generator_grid.grid_rowconfigure(1, weight=1)
            self.generator_grid.grid_rowconfigure(2, weight=0)
            self.generator_grid.grid_columnconfigure(0, weight=1)
            self.generator_grid.grid_columnconfigure(1, weight=0)
            self.config_general_card.grid_configure(row=0, column=0, padx=0, pady=(0, 16))
            self.config_engine_card.grid_configure(row=1, column=0, padx=0, pady=0)
        elif mode == "compact":
            self.topbar_actions.grid_configure(row=1, column=0, columnspan=2, sticky="w", pady=(14, 0))
            self.hero_actions.grid_configure(row=1, column=0, columnspan=2, sticky="w", pady=(18, 0))
            self.generator_left_card.grid_configure(row=0, column=0, padx=0, pady=(0, 16))
            self.generator_right_card.grid_configure(row=1, column=0, rowspan=1, padx=0, pady=(0, 16))
            self.summary_card.grid_configure(row=2, column=0, padx=0, pady=(0, 16))
            self.generator_grid.grid_rowconfigure(0, weight=0)
            self.generator_grid.grid_rowconfigure(1, weight=1)
            self.generator_grid.grid_rowconfigure(2, weight=0)
            self.generator_grid.grid_columnconfigure(0, weight=1)
            self.generator_grid.grid_columnconfigure(1, weight=0)
            self.config_general_card.grid_configure(row=0, column=0, padx=0, pady=(0, 16))
            self.config_engine_card.grid_configure(row=1, column=0, padx=0, pady=0)
        else:
            self.topbar_actions.grid_configure(row=0, column=1, columnspan=1, sticky="e", pady=0)
            self.hero_actions.grid_configure(row=0, column=1, columnspan=1, sticky="e", pady=0)
            self.generator_grid.grid_columnconfigure(0, weight=6 if mode == "wide" else 5)
            self.generator_grid.grid_columnconfigure(1, weight=5 if mode == "wide" else 4)
            self.generator_grid.grid_rowconfigure(0, weight=1)
            self.generator_grid.grid_rowconfigure(1, weight=0)
            self.generator_grid.grid_rowconfigure(2, weight=0)
            self.generator_left_card.grid_configure(row=0, column=0, padx=(0, 10), pady=0)
            self.summary_card.grid_configure(row=1, column=0, padx=(0, 10), pady=(18, 0))
            self.generator_right_card.grid_configure(row=0, column=1, rowspan=2, padx=(10, 0), pady=0)
            self.config_general_card.grid_configure(row=0, column=0, padx=(0, 10), pady=0)
            self.config_engine_card.grid_configure(row=0, column=1, padx=(10, 0), pady=0)

        self._layout_button_group(self.topbar_actions, self.topbar_action_buttons, 1 if mode == "narrow" else 2)
        hero_cols = 3 if mode == "wide" else 2 if mode in ("medium", "compact") else 1
        self._layout_button_group(self.hero_actions, self.hero_action_buttons, hero_cols)
        self._layout_generator_controls(width)
        self._layout_sidebar_text(sidebar_width)
        self._layout_dynamic_text(width)
        self._refresh_content_scrollregion()
        self._refresh_preview()
        return

    def _layout_dynamic_text(self, width: int | None = None):
        if width is None:
            width = self.root.winfo_width()

        mode = self._get_layout_mode(width)
        card_wrap = 520 if mode == "wide" else 420 if mode == "medium" else 320 if mode == "compact" else 240
        hero_wrap = 480 if mode == "wide" else 380 if mode == "medium" else 320 if mode == "compact" else 240
        config_wrap = 440 if mode == "wide" else 360 if mode == "medium" else 300 if mode == "compact" else 240

        if hasattr(self, "page_subtitle"):
            self.page_subtitle.config(wraplength=max(width - 360, 220), justify="left")
        if hasattr(self, "hero_desc"):
            self.hero_desc.config(wraplength=hero_wrap)
        if hasattr(self, "live_feedback_lbl"):
            self.live_feedback_lbl.config(wraplength=max(card_wrap + 40, 260), justify="left")
        if hasattr(self, "barcode_inline_hint"):
            self.barcode_inline_hint.config(wraplength=config_wrap, justify="left")
        if hasattr(self, "_config_detail_labels"):
            for label in self._config_detail_labels:
                label.config(wraplength=config_wrap, justify="left")
        for outer, header, body, title_lbl, subtitle_lbl in self._card_refs:
            subtitle_lbl.config(wraplength=card_wrap)

    def _set_content_mode(self, mode: str):
        self.mode_var.set(mode)
        self.cfg.content_mode = mode
        self._update_mode_ui()
        self._save_config_state(regenerate=True, refresh_text=True)

    def _on_barcode_format_change(self):
        self.cfg.barcode_format = self.barcode_format_var.get()
        self._update_mode_ui()
        self._save_config_state(regenerate=self.mode_var.get() == "Barras", refresh_text=True)

    def _on_barcode_size_change(self):
        if self._syncing_controls:
            return
        self.cfg.barcode_width_name = self.barcode_width_var.get()
        self.cfg.barcode_height_name = self.barcode_height_var.get()
        self._save_config_state(regenerate=self.mode_var.get() == "Barras")

    def _on_barcode_text_toggle(self):
        if self._syncing_controls:
            return
        self.cfg.barcode_show_text = self.barcode_show_text_var.get()
        self._save_config_state(regenerate=self.mode_var.get() == "Barras")

    def _update_mode_ui(self):
        mode = self.mode_var.get()
        if not hasattr(self, "barcode_inline_row"):
            return

        if mode == "Barras":
            self.input_title.config(text="Contenido del código de barras")
            self.input_hint.config(text="Texto alfanumérico para Code 39 o dígitos para EAN / UPC / ITF")
            self.placeholder_lbl.config(
                text="El código de barras aparecerá aquí\n\nEscribe o pega datos y la vista previa se actualizará sola"
            )
            self.btn_generar.config(text="Generar barras")
            self.hero_generate_btn.config(text="Generar barras")
            self.btn_opciones.config(text="Opciones")
            if self.current_qr_img is None:
                self.hero_desc.config(text="Elige un formato de barras y deja que la vista previa te acompañe mientras escribes.")
            if not self.barcode_inline_row.winfo_manager():
                self.barcode_inline_row.pack(fill="x", pady=(0, 12), after=self.mode_row)
        else:
            self.input_title.config(text="Contenido del QR")
            self.input_hint.config(text="URL, texto, WiFi, email, teléfono o vCard")
            self.placeholder_lbl.config(
                text="El código QR aparecerá aquí\n\nEscribe un contenido y la vista previa se actualizará sola"
            )
            self.btn_generar.config(text="Generar QR")
            self.hero_generate_btn.config(text="Generar QR")
            if self.current_qr_img is None:
                self.hero_desc.config(text="Escribe tu contenido y la vista previa se actualiza automáticamente.")
            if self.barcode_inline_row.winfo_manager():
                self.barcode_inline_row.pack_forget()

        barcode_format = self.barcode_format_var.get() or self.cfg.barcode_format
        if barcode_format in ("EAN-13", "EAN-8", "UPC-A"):
            hint = "Puedes escribir sin el último dígito y se calculará automáticamente."
        elif barcode_format == "ITF":
            hint = "ITF usa solo dígitos; si la longitud es impar, se completa con 0 al inicio."
        else:
            hint = "Code 39 admite A-Z, 0-9 y los símbolos - . espacio $ / + %."
        self.barcode_inline_hint.config(text=hint)

    def _build_current_output(self, texto: str):
        mode = self.mode_var.get()
        fill_color = self.cfg.fill_color
        back_color = self.cfg.back_color
        if self.cfg.invert:
            fill_color, back_color = back_color, fill_color

        if mode == "Barras":
            normalized = QREngine.normalize_barcode_data(texto, self.cfg.barcode_format)
            img = QREngine.generate_barcode(
                data=normalized,
                barcode_format=self.cfg.barcode_format,
                fill_color=fill_color,
                back_color=back_color,
                module_width=QREngine.BARCODE_WIDTH_MAP[self.cfg.barcode_width_name],
                height=QREngine.BARCODE_HEIGHT_MAP[self.cfg.barcode_height_name],
                show_text=self.cfg.barcode_show_text,
            )
            dtype = QREngine.detect_barcode_type(self.cfg.barcode_format)
            saved_text = normalized
            output_name = f"codigo_barras_{self.cfg.barcode_format.lower().replace(' ', '_').replace('-', '')}"
            output_label = self.cfg.barcode_format
        else:
            img = QREngine.generate(
                data=texto,
                fill_color=self.cfg.fill_color,
                back_color=self.cfg.back_color,
                box_size=QREngine.SIZE_MAP[self.cfg.size_name],
                error_correction=QREngine.CORRECTION_LEVELS[self.cfg.correction_name],
                invert=self.cfg.invert,
                show_border=self.cfg.show_border,
                logo_path=self.cfg.logo_path if self.cfg.include_logo else None,
                style=self.cfg.qr_style,
            )
            dtype = QREngine.detect_type(texto)
            saved_text = texto
            output_name = "codigo_qr"
            output_label = "QR"

        return img, dtype, saved_text, output_name, output_label

    def _apply_generated_output(self, img, dtype: str, saved_text: str,
                                output_name: str, output_label: str,
                                add_to_history: bool = True):
        self.current_qr_img = img
        self.current_output_name = output_name
        self.current_output_label = output_label
        self._refresh_preview()
        self.btn_guardar.config(state="normal")
        self.btn_exportar_pdf.config(state="normal")
        if add_to_history:
            self.cfg.add_to_history(saved_text, dtype, img)
        self.hero_stats.config(text=f"Código generado: {dtype}")
        self.hero_desc.config(text="Puedes guardarlo, cambiar el diseño o reutilizar el texto desde el historial.")

    def _clear_generated_output(self):
        self.current_qr_img = None
        if self.mode_var.get() == "Barras":
            self.current_output_name = f"codigo_barras_{self.cfg.barcode_format.lower().replace(' ', '_').replace('-', '')}"
            self.current_output_label = self.cfg.barcode_format
        else:
            self.current_output_name = "codigo_qr"
            self.current_output_label = "QR"
        if hasattr(self, "btn_guardar"):
            self.btn_guardar.config(state="disabled")
        if hasattr(self, "btn_exportar_pdf"):
            self.btn_exportar_pdf.config(state="disabled")
        if hasattr(self, "hero_stats"):
            self.hero_stats.config(text="Listo para generar")
        if hasattr(self, "hero_desc"):
            default_desc = (
                "Elige un formato de barras y deja que la vista previa te acompañe mientras escribes."
                if self.mode_var.get() == "Barras"
                else "Escribe tu contenido y la vista previa se actualiza automáticamente."
            )
            self.hero_desc.config(text=default_desc)
        self._refresh_preview()

    def _regenerate_preview_if_possible(self):
        if not hasattr(self, "entrada_texto"):
            return
        texto = self.entrada_texto.get().strip()
        if not texto:
            self._clear_generated_output()
            return
        try:
            img, dtype, saved_text, output_name, output_label = self._build_current_output(texto)
            self._apply_generated_output(
                img, dtype, saved_text, output_name, output_label, add_to_history=False
            )
        except Exception:
            self._clear_generated_output()

    def generar_qr(self):
        texto = self.entrada_texto.get().strip()
        if not texto:
            messagebox.showwarning("Advertencia", "Por favor ingresa un valor para generar el código.")
            return

        try:
            img, dtype, saved_text, output_name, output_label = self._build_current_output(texto)
            self._apply_generated_output(
                img, dtype, saved_text, output_name, output_label, add_to_history=True
            )
            messagebox.showinfo("Éxito", f"Código generado correctamente.\nTipo: {dtype}")
        except Exception as e:
            messagebox.showerror("Error", f"Error al generar el código:\n{e}")

    def _refresh_preview(self, event=None):
        if not hasattr(self, "preview_panel"):
            return
        if self.current_qr_img is None:
            self.label_qr.config(image="")
            self.label_qr.image = None
            self.placeholder_lbl.place(relx=0.5, rely=0.5, anchor="center")
            return

        self.placeholder_lbl.place_forget()
        width = max(self.preview_panel.winfo_width() - 40, 220)
        height = max(self.preview_panel.winfo_height() - 40, 220)
        img_w, img_h = self.current_qr_img.size
        ratio = min(width / max(img_w, 1), height / max(img_h, 1))
        ratio = max(0.1, ratio)
        if img_w < 220 and img_h < 220:
            ratio = min(max(ratio, min(width, height) / max(img_w, img_h)), 2.0)
        new_w = max(1, int(img_w * ratio))
        new_h = max(1, int(img_h * ratio))
        preview = self.current_qr_img.resize((new_w, new_h), Image.Resampling.LANCZOS)
        self._qr_tk = ImageTk.PhotoImage(preview)
        self.label_qr.config(image=self._qr_tk)
        self.label_qr.image = self._qr_tk

    def guardar_qr(self, fmt: str = "png"):
        if self.current_qr_img is None:
            messagebox.showwarning("Aviso", "Primero genera un código.")
            return
        ext = fmt.lower()
        path = filedialog.asksaveasfilename(
            defaultextension=f".{ext}",
            filetypes=[(f"{ext.upper()}", f"*.{ext}"), ("Todos", "*.*")],
            initialfile=f"{self.current_output_name}.{ext}")
        if path:
            try:
                img = self.current_qr_img.convert("RGB") if ext == "jpg" else self.current_qr_img
                img.save(path)
                messagebox.showinfo("Guardado", f"Imagen guardada en:\n{path}")
            except Exception as e:
                messagebox.showerror("Error", str(e))

    def _load_pdf_font(self, size: int, bold: bool = False):
        candidates = ["segoeuib.ttf", "arialbd.ttf", "DejaVuSans-Bold.ttf"] if bold else [
            "segoeui.ttf", "arial.ttf", "DejaVuSans.ttf"
        ]
        for name in candidates:
            try:
                return ImageFont.truetype(name, size)
            except Exception:
                continue
        return ImageFont.load_default()

    def _wrap_pdf_lines(self, draw: ImageDraw.ImageDraw, text: str, font, max_width: int,
                        max_lines: int = 6) -> list[str]:
        if not text:
            return [""]
        words = text.split()
        if not words:
            return [text]

        lines: list[str] = []
        current = words[0]

        def fits(value: str) -> bool:
            left, top, right, bottom = draw.textbbox((0, 0), value, font=font)
            return (right - left) <= max_width

        for word in words[1:]:
            test = f"{current} {word}"
            if fits(test):
                current = test
                continue
            lines.append(current if fits(current) else current[: max(12, len(current) // 2)] + "...")
            current = word
            if len(lines) >= max_lines - 1:
                break

        if len(lines) < max_lines:
            lines.append(current)
        if len(lines) == max_lines and " ".join(words) not in " ".join(lines):
            lines[-1] = lines[-1].rstrip(".") + "..."
        return lines[:max_lines]

    def _build_pdf_page(self) -> Image.Image:
        page_w, page_h = 1240, 1754
        page = Image.new("RGB", (page_w, page_h), "#ffffff")
        draw = ImageDraw.Draw(page)
        title_font = self._load_pdf_font(40, bold=True)
        label_font = self._load_pdf_font(20, bold=True)
        body_font = self._load_pdf_font(24)
        meta_font = self._load_pdf_font(18)

        draw.text((96, 92), f"{self.current_output_label} listo para compartir", fill="#111827", font=title_font)
        draw.text((96, 152), datetime.now().strftime("Exportado el %d/%m/%Y a las %H:%M"),
                  fill="#64748b", font=meta_font)
        draw.rounded_rectangle((80, 220, 1160, 1120), radius=28, outline="#cbd5e1", width=2, fill="#f8fafc")

        img = self.current_qr_img.convert("RGB")
        max_w, max_h = 880, 620
        ratio = min(max_w / max(img.width, 1), max_h / max(img.height, 1))
        size = (max(1, int(img.width * ratio)), max(1, int(img.height * ratio)))
        export_img = img.resize(size, Image.Resampling.LANCZOS)
        img_x = (page_w - size[0]) // 2
        img_y = 300 + max((560 - size[1]) // 2, 0)
        page.paste(export_img, (img_x, img_y))

        draw.text((96, 1180), "Contenido", fill="#0f172a", font=label_font)
        source_text = self.entrada_texto.get().strip()
        for idx, line in enumerate(self._wrap_pdf_lines(draw, source_text, body_font, 1040, max_lines=8)):
            draw.text((96, 1232 + idx * 38), line, fill="#1f2937", font=body_font)

        footer = "Generado desde QR Pro"
        left, top, right, bottom = draw.textbbox((0, 0), footer, font=meta_font)
        draw.text((page_w - (right - left) - 96, page_h - 86), footer, fill="#94a3b8", font=meta_font)
        return page

    def exportar_pdf(self):
        if self.current_qr_img is None:
            messagebox.showwarning("Aviso", "Primero genera un código.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF", "*.pdf"), ("Todos", "*.*")],
            initialfile=f"{self.current_output_name}.pdf",
        )
        if not path:
            return
        try:
            self._build_pdf_page().save(path, "PDF", resolution=150.0)
            messagebox.showinfo("PDF exportado", f"Archivo guardado en:\n{path}")
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo exportar el PDF:\n{e}")

    def limpiar(self):
        self._cancel_preview_regeneration()
        self.entrada_texto.delete(0, tk.END)
        self.cfg.last_text = ""
        self.cfg.save()
        self._clear_generated_output()
        self.type_lbl.config(text="Tipo: —")
        self._set_live_feedback(self._feedback_default, "neutral")
        self._update_mode_ui()
        self._refresh_preview()

    def _open_scan(self):
        ScanWindow(self.root, self.theme)

    def _scan_inline(self):
        path = filedialog.askopenfilename(
            title="Seleccionar imagen con código",
            filetypes=[("Imágenes", "*.png *.jpg *.jpeg *.bmp *.gif"), ("Todos", "*.*")])
        if not path:
            return
        self._scan_image_path(path)

    def _render_scan_results(self, results: list[dict]):
        self.scan_text.config(state="normal")
        self.scan_text.delete("1.0", "end")
        if results:
            self.scan_result_text = results[0]["text"]
            for i, r in enumerate(results, 1):
                self.scan_text.insert("end", f"Código #{i} [{r['type']}]:\n{r['text']}\n\n")
        else:
            self.scan_result_text = ""
            self.scan_text.insert("end", "No se encontró ningún código legible en la imagen.\nAsegúrate de que sea clara y legible.")
        self.scan_text.config(state="disabled")

    def _scan_image_path(self, path: str):
        self._render_scan_results(QREngine.scan_image(path))

    def _handle_scan_drop(self, event):
        path = self._extract_drop_path(event.data)
        if not path:
            messagebox.showwarning("Archivo no válido", "Suelta una sola imagen compatible para escanear.")
            return
        self._scan_image_path(path)

    def _use_scan_result(self):
        if not self.scan_result_text:
            messagebox.showwarning("Sin resultado", "Primero escanea una imagen con un código.")
            return
        self._switch_page("Generador QR")
        self._set_input_text(self.scan_result_text)

    def _refresh_history_tree(self):
        self.hist_tree.delete(*self.hist_tree.get_children())
        for entry in self.cfg.history:
            short = entry["text"][:70] + ("…" if len(entry["text"]) > 70 else "")
            tag = "" if entry.get("img_bytes") else "  🔗"
            self.hist_tree.insert("", "end", values=(short + tag, entry["type"], entry["timestamp"]))

    def _save_history_item(self):
        sel = self.hist_tree.selection()
        if not sel:
            messagebox.showwarning("Sin selección", "Selecciona un código del historial.")
            return
        entry = self.cfg.history[self.hist_tree.index(sel[0])]
        if not entry.get("img_bytes"):
            messagebox.showwarning("Sin imagen", "Este registro no tiene imagen almacenada.\nGenera el código de nuevo.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("PNG", "*.png"), ("JPEG", "*.jpg"), ("Todos", "*.*")],
            initialfile="codigo_historial.png")
        if path:
            img = Image.open(io.BytesIO(entry["img_bytes"]))
            ext = os.path.splitext(path)[1].lower()
            if ext in (".jpg", ".jpeg"):
                img = img.convert("RGB")
            img.save(path)
            messagebox.showinfo("Guardado", f"Guardado en:\n{path}")

    def _clear_history(self):
        if messagebox.askyesno("Borrar historial", "¿Seguro que deseas borrar todo el historial?"):
            self.cfg.history.clear()
            self.cfg.save()
            self._refresh_history_tree()

    def _open_stats(self):
        if not self.cfg.history:
            messagebox.showinfo("Estadísticas", "El historial está vacío.")
            return
        StatsWindow(self.root, self.cfg.history, self.theme)

    def _on_text_change(self, event=None, schedule_preview: bool = True):
        text = self.entrada_texto.get().strip()
        self.cfg.last_text = self.entrada_texto.get()
        self.cfg.save()
        if not text:
            dtype = "—"
        elif self.mode_var.get() == "Barras":
            dtype = QREngine.detect_barcode_type(self.cfg.barcode_format)
        else:
            dtype = QREngine.detect_type(text)
        self.type_lbl.config(text=f"Tipo: {dtype}")
        message, state = self._describe_live_input(text)
        self._set_live_feedback(message, state)
        if schedule_preview:
            self._schedule_preview_regeneration()

    def _copy_text(self):
        self.root.clipboard_clear()
        self.root.clipboard_append(self.entrada_texto.get())

    def _paste_text(self):
        try:
            self._set_input_text(self.root.clipboard_get())
        except Exception:
            pass

    def _show_context_menu(self, event):
        self.context_menu.tk_popup(event.x_root, event.y_root)

    def _open_options(self):
        OptionsWindow(self.root, self.cfg, self._on_options_applied, self.theme)

    def _on_options_applied(self):
        self._sync_config_controls()
        self._update_mode_ui()
        self._save_config_state(regenerate=True, refresh_text=True, rebuild_presets=True)

    def _sync_config_controls(self):
        self._syncing_controls = True
        try:
            self.var_border.set(self.cfg.show_border)
            self.var_invert.set(self.cfg.invert)
            self.var_dark_theme.set(self.cfg.dark_theme)
            self.mode_var.set(self.cfg.content_mode)
            self.barcode_format_var.set(self.cfg.barcode_format)
            self.barcode_width_var.set(self.cfg.barcode_width_name)
            self.barcode_height_var.set(self.cfg.barcode_height_name)
            self.barcode_show_text_var.set(self.cfg.barcode_show_text)
            if hasattr(self, "corr_var_cfg"):
                self.corr_var_cfg.set(self.cfg.correction_name)
            if hasattr(self, "size_var_cfg"):
                self.size_var_cfg.set(self.cfg.size_name)
            if hasattr(self, "style_var_cfg"):
                self.style_var_cfg.set(self.cfg.qr_style)
        finally:
            self._syncing_controls = False

    def _update_config_preview(self):
        if not hasattr(self, "cfg_fill_preview"):
            return
        self.cfg_fill_preview.config(bg=self.cfg.fill_color)
        self.cfg_back_preview.config(bg=self.cfg.back_color)
        self.cfg_mode_lbl.config(text=f"Modo: {self.cfg.content_mode}")
        self.cfg_size_lbl.config(text=f"Tamaño QR: {self.cfg.size_name}")
        self.cfg_style_lbl.config(text=f"Estilo QR: {self.cfg.qr_style}")
        self.cfg_corr_lbl.config(text=f"Corrección QR: {self.cfg.correction_name.split('–')[0].strip()}")
        self.cfg_barcode_lbl.config(
            text=f"Barras: {self.cfg.barcode_format} · texto {'sí' if self.cfg.barcode_show_text else 'no'}"
        )
        self.cfg_barcode_size_lbl.config(
            text=f"Grosor/altura barras: {self.cfg.barcode_width_name} / {self.cfg.barcode_height_name}"
        )

    def _quick_color(self, hx):
        self.cfg.fill_color = hx
        self._save_config_state(regenerate=True)

    def _quick_size(self, name):
        self.cfg.size_name = name
        self._save_config_state(sync_controls=True, regenerate=self.mode_var.get() == "QR")

    def _quick_style(self, name):
        self.cfg.qr_style = name
        self._save_config_state(sync_controls=True, regenerate=self.mode_var.get() == "QR")

    def _set_default_size(self, value):
        self.cfg.size_name = value
        self._save_config_state(regenerate=self.mode_var.get() == "QR")

    def _set_default_style(self, value):
        self.cfg.qr_style = value
        self._save_config_state(regenerate=self.mode_var.get() == "QR")

    def _toggle_border(self):
        self.cfg.show_border = self.var_border.get()
        self._save_config_state(regenerate=self.mode_var.get() == "QR")

    def _toggle_invert(self):
        self.cfg.invert = self.var_invert.get()
        self._save_config_state(regenerate=True)

    def _toggle_theme(self):
        self.cfg.dark_theme = self.var_dark_theme.get()
        self.theme = DARK if self.cfg.dark_theme else LIGHT
        self.cfg.save()
        self._apply_theme()

    def _open_form_builder(self):
        FormBuilderWindow(self.root, self._on_form_result, self.theme)

    def _on_form_result(self, text: str):
        self._switch_page("Generador QR")
        self._set_input_text(text)

    def _rebuild_presets_menu(self):
        self.m_presets.delete(0, "end")
        if not self.cfg.presets:
            self.m_presets.add_command(label="(sin presets guardados)", state="disabled")
            return
        for p in self.cfg.presets:
            self.m_presets.add_command(label=p["name"], command=lambda n=p["name"]: self._load_preset(n))

    def _load_preset(self, name: str):
        if self.cfg.load_preset(name):
            self._on_options_applied()
            messagebox.showinfo("Preset cargado", f"Preset '{name}' aplicado.")

    def _show_instructions(self):
        win = tk.Toplevel(self.root)
        win.title("Instrucciones")
        win.geometry("520x420")
        win.grab_set()
        win.configure(bg=self.theme["bg"])
        tk.Label(win, text="Cómo usar QR Pro", font=("Segoe UI", 14, "bold"),
                 bg=self.theme["bg"], fg=self.theme["fg"]).pack(pady=(18, 10))
        text = (
            "1. Elige entre QR o Código de barras.\n\n"
            "2. Escribe un enlace, texto, WiFi, email, vCard o datos numéricos para barras.\n\n"
            "3. Ajusta colores, estilo, tamaño, logo y formato de barras desde Opciones.\n\n"
            "4. Guarda el resultado en PNG o JPG.\n\n"
            "5. Usa el lector para extraer contenido de imágenes.\n\n"
            "6. Cambia entre modo maximizado y pantalla completa con F11."
        )
        tk.Label(win, text=text, font=("Segoe UI", 10), justify="left",
                 wraplength=460, bg=self.theme["bg"], fg=self.theme["fg"]).pack(padx=24)
        self._mkbtn(win, "Cerrar", BTN_GREY_L, win.destroy, padx=18, pady=8).pack(pady=18)

    def _confirm_exit(self):
        if messagebox.askyesno("Salir", "¿Deseas cerrar la aplicación?"):
            self.cfg.save()
            self.root.destroy()

    def _apply_theme(self):
        t = self.theme

        accent_map = {
            BTN_GREEN_D: BTN_GREEN_D if t == DARK else BTN_GREEN_L,
            BTN_GREEN_L: BTN_GREEN_D if t == DARK else BTN_GREEN_L,
            BTN_BLUE_D: BTN_BLUE_D if t == DARK else BTN_BLUE_L,
            BTN_BLUE_L: BTN_BLUE_D if t == DARK else BTN_BLUE_L,
            BTN_RED_D: BTN_RED_D if t == DARK else BTN_RED_L,
            BTN_RED_L: BTN_RED_D if t == DARK else BTN_RED_L,
            BTN_PURPLE_D: BTN_PURPLE_D if t == DARK else BTN_PURPLE_L,
            BTN_PURPLE_L: BTN_PURPLE_D if t == DARK else BTN_PURPLE_L,
            BTN_GREY_D: BTN_GREY_D if t == DARK else BTN_GREY_L,
            BTN_GREY_L: BTN_GREY_D if t == DARK else BTN_GREY_L,
            BTN_TEAL_D: BTN_TEAL_D if t == DARK else BTN_TEAL_L,
            BTN_TEAL_L: BTN_TEAL_D if t == DARK else BTN_TEAL_L,
        }

        def tint_subtree(widget, bg, fg=None):
            try:
                cls = widget.winfo_class()
                if cls in ("Frame", "LabelFrame"):
                    widget.config(bg=bg)
                elif cls == "Label":
                    widget.config(bg=bg, fg=fg or t["fg"])
                elif cls == "Entry":
                    widget.config(bg=t["entry_bg"], fg=t["fg"], insertbackground=t["fg"])
                elif cls == "Text":
                    widget.config(bg=t["entry_bg"], fg=t["fg"], insertbackground=t["fg"])
                elif cls == "Radiobutton":
                    widget.config(bg=bg, fg=fg or t["fg"], selectcolor=t["check_sel"], activebackground=bg)
                elif cls == "Checkbutton":
                    widget.config(bg=bg, fg=fg or t["fg"], selectcolor=t["check_sel"], activebackground=bg)
            except Exception:
                pass
            for child in widget.winfo_children():
                tint_subtree(child, bg, fg)

        def paint(widget):
            cls = widget.winfo_class()
            try:
                if cls in ("Frame", "LabelFrame"):
                    widget.config(bg=t["bg"], highlightbackground=t["border"], highlightcolor=t["border"])
                elif cls == "Label":
                    widget.config(bg=t["bg"], fg=t["fg"])
                elif cls == "Entry":
                    widget.config(bg=t["entry_bg"], fg=t["fg"], insertbackground=t["fg"])
                elif cls == "Text":
                    widget.config(bg=t["entry_bg"], fg=t["fg"], insertbackground=t["fg"])
                elif cls == "Radiobutton":
                    widget.config(bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"], activebackground=t["bg"])
                elif cls == "Checkbutton":
                    widget.config(bg=t["bg"], fg=t["fg"], selectcolor=t["check_sel"], activebackground=t["bg"])
                elif cls == "Button":
                    base = getattr(widget, "_accent_source", widget.cget("bg"))
                    if base in accent_map:
                        tone = accent_map[base]
                        self._register_hover_button(widget)
                        self._set_button_palette(widget, tone, shift_hex(tone, 0.14), "white")
                    else:
                        self._register_hover_button(widget)
                        self._set_button_palette(widget, t["btn_bg"], t["card2"], t["fg"])
            except Exception:
                pass
            for child in widget.winfo_children():
                paint(child)

        self.root.configure(bg=t["bg"])
        paint(self.root)

        self.sidebar.config(bg=t["sidebar"])
        self.main_shell.config(bg=t["bg"])
        self.content_shell.config(bg=t["bg"])
        self.content_canvas.config(bg=t["bg"], highlightbackground=t["bg"])
        self.content.config(bg=t["bg"])
        self.topbar.config(bg=t["bg"])
        self.brand_card.config(bg=t["sidebar"])
        self.brand_icon.config(bg=t["red"], fg="white")
        self.brand_title.config(bg=t["sidebar"], fg=t["fg"])
        self.brand_subtitle.config(bg=t["sidebar"], fg=t["subtext"])
        tint_subtree(self.sidebar, t["sidebar"], t["fg"])
        self.brand_icon.config(bg=t["red"], fg="white")
        self.quick_box.config(bg=t["card"], highlightbackground=t["border"], highlightthickness=1)
        self.quick_title.config(bg=t["card"], fg=t["subtext"])
        self.side_footer.config(bg=t["sidebar"])
        self.footer_hint.config(bg=t["sidebar"], fg=t["subtext"])
        self.nav_section_label.config(bg=self.sidebar.cget("bg"), fg=t["subtext"])

        for outer, header, body, title_lbl, subtitle_lbl in self._card_refs:
            outer.config(bg=t["card"], highlightbackground=t["border"])
            header.config(bg=t["card"])
            body.config(bg=t["card"])
            tint_subtree(body, t["card"], t["fg"])
            title_lbl.config(bg=t["card"], fg=t["fg"])
            subtitle_lbl.config(bg=t["card"], fg=t["subtext"])

        self.page_title.config(bg=t["bg"], fg=t["fg"])
        self.page_subtitle.config(bg=t["bg"], fg=t["subtext"])
        self.hero_stats.config(bg=t["card"], fg=t["blue"])
        self.hero_desc.config(bg=t["card"], fg=t["fg"])
        self.input_title.config(bg=t["card"], fg=t["fg"])
        self.input_hint.config(bg=t["card"], fg=t["subtext"])
        self.type_lbl.config(bg=t["card"], fg=t["subtext"])
        if hasattr(self, "live_feedback_lbl"):
            self.live_feedback_lbl.config(bg=t["card"])
            self._set_live_feedback(self.live_feedback_lbl.cget("text"), self._feedback_state)
        if hasattr(self, "scan_drop_zone"):
            self.scan_drop_zone.config(bg=t["card2"], fg=t["fg"])
        self.label_qr.config(bg=t["card"])
        self.preview_panel.config(bg=t["card"])
        self.placeholder_lbl.config(bg=t["card"], fg=t["subtext"])

        style = ttk.Style()
        style.theme_use("default")
        style.configure("Treeview", background=t["entry_bg"], foreground=t["fg"],
                        fieldbackground=t["entry_bg"], rowheight=28, borderwidth=0)
        style.configure("Treeview.Heading", background=t["card2"], foreground=t["fg"], relief="flat")
        style.map("Treeview", background=[("selected", t["blue"])], foreground=[("selected", "#ffffff")])
        style.configure("TCombobox", fieldbackground=t["entry_bg"], background=t["btn_bg"],
                        foreground=t["fg"], arrowcolor=t["fg"])
        style.map("TCombobox", fieldbackground=[("readonly", t["entry_bg"])], foreground=[("readonly", t["fg"])])
        style.configure("Vertical.TScrollbar", background=t["btn_bg"], troughcolor=t["bg"], arrowcolor=t["fg"])

        self._sync_config_controls()
        self._update_config_preview()
        self._update_nav_buttons()
        self._refresh_preview()


# ══════════════════════════════════════════════════════════════
#  ENTRADA
# ══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    root = TkinterDnD.Tk() if TKDND_OK else tk.Tk()
    app = GeneradorQR(root)
    root.mainloop()
