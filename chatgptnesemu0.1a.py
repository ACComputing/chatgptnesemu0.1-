#!/usr/bin/env python3
"""
chatgptsnesemu0.1.py

A single-file, clean-room NES emulator with a Tkinter GUI.

What this version does:
  * Loads iNES .nes ROMs from disk.
  * Includes a tiny built-in NROM demo ROM so the emulator can boot without
    shipping copyrighted game data.
  * Emulates the 2A03/6502 CPU, PPU register interface, controller input,
    nametable/palette/OAM memory, DMA, and several common mappers.
  * Supports mappers 0, 1, 2, 3, 4, 7, and 66 at a pragmatic level.
  * Renders background and sprites through Tkinter. Audio is stubbed.

Controls:
  A      = Z
  B      = X
  Select = Right Shift / Left Shift
  Start  = Enter
  D-pad  = Arrow keys
  Pause  = P
  Reset  = R
  Turbo  = Tab while held

Run:
  python3 chatgptsnesemu0.1.py
  python3 chatgptsnesemu0.1.py path/to/game.nes
  python3 chatgptsnesemu0.1.py --demo

Notes:
  This is educational software. It does not include copyrighted ROMs.
  Use only ROMs you are legally allowed to run.
"""

from __future__ import annotations

import argparse
import base64
import math
import os
import sys
import time
import tkinter as tk
from tkinter import filedialog, messagebox
from dataclasses import dataclass
from typing import Optional, Tuple, Dict, List

# ---------------------------------------------------------------------------
# NES palette: commonly used NTSC approximation, 64 colors.
# ---------------------------------------------------------------------------
NES_PALETTE: List[Tuple[int, int, int]] = [
    (84, 84, 84), (0, 30, 116), (8, 16, 144), (48, 0, 136),
    (68, 0, 100), (92, 0, 48), (84, 4, 0), (60, 24, 0),
    (32, 42, 0), (8, 58, 0), (0, 64, 0), (0, 60, 0),
    (0, 50, 60), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (152, 150, 152), (8, 76, 196), (48, 50, 236), (92, 30, 228),
    (136, 20, 176), (160, 20, 100), (152, 34, 32), (120, 60, 0),
    (84, 90, 0), (40, 114, 0), (8, 124, 0), (0, 118, 40),
    (0, 102, 120), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (76, 154, 236), (120, 124, 236), (176, 98, 236),
    (228, 84, 236), (236, 88, 180), (236, 106, 100), (212, 136, 32),
    (160, 170, 0), (116, 196, 0), (76, 208, 32), (56, 204, 108),
    (56, 180, 204), (60, 60, 60), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (168, 204, 236), (188, 188, 236), (212, 178, 236),
    (236, 174, 236), (236, 174, 212), (236, 180, 176), (228, 196, 144),
    (204, 210, 120), (180, 222, 120), (168, 226, 144), (152, 226, 180),
    (160, 214, 228), (160, 162, 160), (0, 0, 0), (0, 0, 0),
]

# ---------------------------------------------------------------------------
# Cartridge / mapper support
# ---------------------------------------------------------------------------

class CartridgeError(Exception):
    pass


class Cartridge:
    """iNES cartridge loader plus a compact set of mapper implementations."""

    SUPPORTED_MAPPERS = {0, 1, 2, 3, 4, 7, 66}

    def __init__(self, data: bytes, name: str = "<memory>"):
        self.name = name
        if len(data) < 16 or data[:4] != b"NES\x1a":
            raise CartridgeError("Not an iNES ROM: missing NES<EOF> header")

        self.prg_banks_16k = data[4]
        self.chr_banks_8k = data[5]
        flags6 = data[6]
        flags7 = data[7]
        self.mapper = (flags6 >> 4) | (flags7 & 0xF0)
        self.has_trainer = bool(flags6 & 0x04)
        self.has_battery = bool(flags6 & 0x02)
        self.four_screen = bool(flags6 & 0x08)

        if self.four_screen:
            self.mirroring = "four"
        else:
            self.mirroring = "vertical" if (flags6 & 1) else "horizontal"

        offset = 16 + (512 if self.has_trainer else 0)
        prg_size = self.prg_banks_16k * 0x4000
        chr_size = self.chr_banks_8k * 0x2000
        if len(data) < offset + prg_size + chr_size:
            raise CartridgeError("ROM is truncated")

        self.prg = bytearray(data[offset: offset + prg_size])
        offset += prg_size
        if self.chr_banks_8k:
            self.chr = bytearray(data[offset: offset + chr_size])
            self.chr_ram = False
        else:
            self.chr = bytearray(0x2000)
            self.chr_ram = True

        self.prg_ram = bytearray(0x2000)
        self.warning = ""
        if self.mapper not in self.SUPPORTED_MAPPERS:
            self.warning = (
                f"Mapper {self.mapper} is not implemented. The emulator will try "
                "a simple NROM-style fallback, but the ROM probably will not run."
            )

        # Mapper 1 / MMC1 state
        self.mmc1_shift = 0x10
        self.mmc1_control = 0x0C
        self.mmc1_chr0 = 0
        self.mmc1_chr1 = 0
        self.mmc1_prg = 0

        # Mapper 2 / UxROM
        self.uxrom_bank = 0

        # Mapper 3 / CNROM
        self.cnrom_chr_bank = 0

        # Mapper 4 / MMC3 state
        self.mmc3_bank_select = 0
        self.mmc3_regs = [0] * 8
        self.mmc3_prg_mode = 0
        self.mmc3_chr_mode = 0
        self.mmc3_irq_latch = 0
        self.mmc3_irq_counter = 0
        self.mmc3_irq_reload = False
        self.mmc3_irq_enable = False
        self.irq_pending = False

        # Mapper 7 / AxROM
        self.axrom_bank = 0

        # Mapper 66 / GxROM
        self.gxrom_prg_bank = 0
        self.gxrom_chr_bank = 0

    @classmethod
    def from_file(cls, path: str) -> "Cartridge":
        with open(path, "rb") as f:
            return cls(f.read(), os.path.basename(path))

    @property
    def prg16_count(self) -> int:
        return max(1, len(self.prg) // 0x4000)

    @property
    def prg8_count(self) -> int:
        return max(1, len(self.prg) // 0x2000)

    @property
    def prg32_count(self) -> int:
        return max(1, len(self.prg) // 0x8000)

    @property
    def chr1_count(self) -> int:
        return max(1, len(self.chr) // 0x0400)

    @property
    def chr4_count(self) -> int:
        return max(1, len(self.chr) // 0x1000)

    @property
    def chr8_count(self) -> int:
        return max(1, len(self.chr) // 0x2000)

    def _prg_read_16k(self, bank: int, addr: int) -> int:
        bank %= self.prg16_count
        off = bank * 0x4000 + (addr & 0x3FFF)
        return self.prg[off % len(self.prg)]

    def _prg_read_8k(self, bank: int, addr: int) -> int:
        bank %= self.prg8_count
        off = bank * 0x2000 + (addr & 0x1FFF)
        return self.prg[off % len(self.prg)]

    def _prg_read_32k(self, bank: int, addr: int) -> int:
        bank %= self.prg32_count
        off = bank * 0x8000 + (addr & 0x7FFF)
        return self.prg[off % len(self.prg)]

    def cpu_read(self, addr: int) -> int:
        addr &= 0xFFFF
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[(addr - 0x6000) & 0x1FFF]
        if addr < 0x8000:
            return 0

        if self.mapper == 0 or self.mapper not in self.SUPPORTED_MAPPERS:
            if self.prg16_count == 1:
                return self._prg_read_16k(0, addr)
            return self._prg_read_32k(0, addr)

        if self.mapper == 2:
            if addr < 0xC000:
                return self._prg_read_16k(self.uxrom_bank, addr)
            return self._prg_read_16k(self.prg16_count - 1, addr)

        if self.mapper == 3:
            if self.prg16_count == 1:
                return self._prg_read_16k(0, addr)
            return self._prg_read_32k(0, addr)

        if self.mapper == 1:
            mode = (self.mmc1_control >> 2) & 3
            bank = self.mmc1_prg & 0x0F
            if mode in (0, 1):
                return self._prg_read_32k(bank >> 1, addr)
            if mode == 2:
                if addr < 0xC000:
                    return self._prg_read_16k(0, addr)
                return self._prg_read_16k(bank, addr)
            if addr < 0xC000:
                return self._prg_read_16k(bank, addr)
            return self._prg_read_16k(self.prg16_count - 1, addr)

        if self.mapper == 4:
            return self._mmc3_cpu_read(addr)

        if self.mapper == 7:
            return self._prg_read_32k(self.axrom_bank, addr)

        if self.mapper == 66:
            return self._prg_read_32k(self.gxrom_prg_bank, addr)

        return 0

    def cpu_write(self, addr: int, value: int) -> None:
        addr &= 0xFFFF
        value &= 0xFF
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[(addr - 0x6000) & 0x1FFF] = value
            return
        if addr < 0x8000:
            return

        if self.mapper == 0 or self.mapper not in self.SUPPORTED_MAPPERS:
            return

        if self.mapper == 2:
            self.uxrom_bank = value % self.prg16_count
            return

        if self.mapper == 3:
            self.cnrom_chr_bank = value % self.chr8_count
            return

        if self.mapper == 1:
            self._mmc1_write(addr, value)
            return

        if self.mapper == 4:
            self._mmc3_write(addr, value)
            return

        if self.mapper == 7:
            self.axrom_bank = value & 0x07
            self.mirroring = "one1" if (value & 0x10) else "one0"
            return

        if self.mapper == 66:
            self.gxrom_prg_bank = (value >> 4) & 0x03
            self.gxrom_chr_bank = value & 0x03
            return

    def ppu_read(self, addr: int) -> int:
        addr &= 0x1FFF
        off = self._chr_offset(addr)
        return self.chr[off % len(self.chr)]

    def ppu_write(self, addr: int, value: int) -> None:
        addr &= 0x1FFF
        value &= 0xFF
        # CHR RAM cartridges are writable. Some mapper test ROMs also expect
        # writes to be harmless even when CHR is ROM.
        if self.chr_ram:
            off = self._chr_offset(addr)
            self.chr[off % len(self.chr)] = value

    def _chr_offset(self, addr: int) -> int:
        if self.mapper == 3:
            return (self.cnrom_chr_bank % self.chr8_count) * 0x2000 + addr

        if self.mapper == 1:
            chr_mode = (self.mmc1_control >> 4) & 1
            if chr_mode == 0:
                bank = (self.mmc1_chr0 & 0x1E) % max(1, self.chr4_count)
                return bank * 0x1000 + addr
            if addr < 0x1000:
                return (self.mmc1_chr0 % self.chr4_count) * 0x1000 + (addr & 0x0FFF)
            return (self.mmc1_chr1 % self.chr4_count) * 0x1000 + (addr & 0x0FFF)

        if self.mapper == 4:
            return self._mmc3_chr_offset(addr)

        if self.mapper == 66:
            return (self.gxrom_chr_bank % self.chr8_count) * 0x2000 + addr

        return addr

    def _mmc1_write(self, addr: int, value: int) -> None:
        if value & 0x80:
            self.mmc1_shift = 0x10
            self.mmc1_control |= 0x0C
            return
        complete = self.mmc1_shift & 1
        self.mmc1_shift = (self.mmc1_shift >> 1) | ((value & 1) << 4)
        if complete:
            reg_value = self.mmc1_shift & 0x1F
            area = (addr >> 13) & 0x03
            if area == 0:
                self.mmc1_control = reg_value
                mir = reg_value & 0x03
                if mir == 0:
                    self.mirroring = "one0"
                elif mir == 1:
                    self.mirroring = "one1"
                elif mir == 2:
                    self.mirroring = "vertical"
                else:
                    self.mirroring = "horizontal"
            elif area == 1:
                self.mmc1_chr0 = reg_value
            elif area == 2:
                self.mmc1_chr1 = reg_value
            else:
                self.mmc1_prg = reg_value
            self.mmc1_shift = 0x10

    def _mmc3_cpu_read(self, addr: int) -> int:
        r6 = self.mmc3_regs[6]
        r7 = self.mmc3_regs[7]
        last = self.prg8_count - 1
        second_last = self.prg8_count - 2
        if self.mmc3_prg_mode == 0:
            if addr < 0xA000:
                return self._prg_read_8k(r6, addr)
            if addr < 0xC000:
                return self._prg_read_8k(r7, addr)
            if addr < 0xE000:
                return self._prg_read_8k(second_last, addr)
            return self._prg_read_8k(last, addr)
        if addr < 0xA000:
            return self._prg_read_8k(second_last, addr)
        if addr < 0xC000:
            return self._prg_read_8k(r7, addr)
        if addr < 0xE000:
            return self._prg_read_8k(r6, addr)
        return self._prg_read_8k(last, addr)

    def _mmc3_write(self, addr: int, value: int) -> None:
        even = (addr & 1) == 0
        region = addr & 0xE001
        if region == 0x8000:
            self.mmc3_bank_select = value & 0x07
            self.mmc3_prg_mode = (value >> 6) & 1
            self.mmc3_chr_mode = (value >> 7) & 1
        elif region == 0x8001:
            self.mmc3_regs[self.mmc3_bank_select] = value
        elif region == 0xA000:
            # MMC3 ignores mirroring when four-screen is wired on the board.
            if not self.four_screen:
                self.mirroring = "horizontal" if (value & 1) else "vertical"
        elif region == 0xA001:
            pass  # PRG RAM protect; ignored.
        elif region == 0xC000:
            self.mmc3_irq_latch = value
        elif region == 0xC001:
            self.mmc3_irq_reload = True
        elif region == 0xE000:
            self.mmc3_irq_enable = False
            self.irq_pending = False
        elif region == 0xE001:
            self.mmc3_irq_enable = True

    def _mmc3_chr_offset(self, addr: int) -> int:
        a = addr & 0x1FFF
        # Returns a 1KB bank offset.
        if self.mmc3_chr_mode == 0:
            if a < 0x0800:
                bank = (self.mmc3_regs[0] & 0xFE) + ((a >> 10) & 1)
            elif a < 0x1000:
                bank = (self.mmc3_regs[1] & 0xFE) + ((a >> 10) & 1)
            elif a < 0x1400:
                bank = self.mmc3_regs[2]
            elif a < 0x1800:
                bank = self.mmc3_regs[3]
            elif a < 0x1C00:
                bank = self.mmc3_regs[4]
            else:
                bank = self.mmc3_regs[5]
        else:
            if a < 0x0400:
                bank = self.mmc3_regs[2]
            elif a < 0x0800:
                bank = self.mmc3_regs[3]
            elif a < 0x0C00:
                bank = self.mmc3_regs[4]
            elif a < 0x1000:
                bank = self.mmc3_regs[5]
            elif a < 0x1800:
                bank = (self.mmc3_regs[0] & 0xFE) + ((a >> 10) & 1)
            else:
                bank = (self.mmc3_regs[1] & 0xFE) + ((a >> 10) & 1)
        return (bank % self.chr1_count) * 0x400 + (a & 0x03FF)

    def clock_scanline(self) -> None:
        if self.mapper != 4:
            return
        if self.mmc3_irq_counter == 0 or self.mmc3_irq_reload:
            self.mmc3_irq_counter = self.mmc3_irq_latch
            self.mmc3_irq_reload = False
        else:
            self.mmc3_irq_counter = (self.mmc3_irq_counter - 1) & 0xFF
        if self.mmc3_irq_counter == 0 and self.mmc3_irq_enable:
            self.irq_pending = True

    @property
    def mapper_name(self) -> str:
        names = {
            0: "NROM",
            1: "MMC1",
            2: "UxROM",
            3: "CNROM",
            4: "MMC3",
            7: "AxROM",
            66: "GxROM",
        }
        return names.get(self.mapper, f"Mapper {self.mapper}")


# ---------------------------------------------------------------------------
# Controllers
# ---------------------------------------------------------------------------

class Controller:
    BUTTON_ORDER = ["A", "B", "Select", "Start", "Up", "Down", "Left", "Right"]

    def __init__(self) -> None:
        self.state = {name: False for name in self.BUTTON_ORDER}
        self.shift = 0
        self.strobe = 0

    def set_button(self, button: str, pressed: bool) -> None:
        if button in self.state:
            self.state[button] = bool(pressed)

    def latch(self) -> None:
        value = 0
        for i, name in enumerate(self.BUTTON_ORDER):
            if self.state[name]:
                value |= 1 << i
        # Avoid impossible D-pad pairs; many games assume a real controller.
        if self.state["Left"] and self.state["Right"]:
            value &= ~((1 << 6) | (1 << 7))
        if self.state["Up"] and self.state["Down"]:
            value &= ~((1 << 4) | (1 << 5))
        self.shift = value

    def write_strobe(self, value: int) -> None:
        old = self.strobe
        self.strobe = value & 1
        if self.strobe:
            self.latch()
        elif old and not self.strobe:
            self.latch()

    def read(self) -> int:
        if self.strobe:
            self.latch()
        result = self.shift & 1
        if not self.strobe:
            self.shift = (self.shift >> 1) | 0x80
        return 0x40 | result


# ---------------------------------------------------------------------------
# PPU
# ---------------------------------------------------------------------------

class PPU:
    WIDTH = 256
    HEIGHT = 240

    def __init__(self, cart: Cartridge, bus: "Bus") -> None:
        self.cart = cart
        self.bus = bus
        self.vram = bytearray(0x1000 if cart.mirroring == "four" else 0x800)
        self.palette_ram = bytearray(0x20)
        self.oam = bytearray(0x100)
        self.oam_addr = 0

        self.ctrl = 0
        self.mask = 0
        self.status = 0xA0
        self.vram_addr = 0
        self.temp_addr = 0
        self.addr_latch = 0
        self.read_buffer = 0
        self.scroll_x = 0
        self.scroll_y = 0

        self.scanline = 0
        self.dot = 0
        self.frame_counter = 0
        self.frame_rgb = bytearray(self.WIDTH * self.HEIGHT * 3)
        self.bg_opaque = bytearray(self.WIDTH * self.HEIGHT)
        self.sprite0_hit: Optional[Tuple[int, int]] = None

        self._fill_color(0)

    def _fill_color(self, palette_index: int) -> None:
        r, g, b = NES_PALETTE[palette_index & 0x3F]
        rgb = self.frame_rgb
        for i in range(0, len(rgb), 3):
            rgb[i] = r
            rgb[i + 1] = g
            rgb[i + 2] = b

    def cpu_read_register(self, addr: int) -> int:
        reg = addr & 7
        if reg == 2:  # PPUSTATUS
            value = (self.status & 0xE0) | (self.read_buffer & 0x1F)
            self.status &= ~0x80
            self.addr_latch = 0
            self.bus.nmi_pending = False
            return value
        if reg == 4:  # OAMDATA
            return self.oam[self.oam_addr]
        if reg == 7:  # PPUDATA
            addr0 = self.vram_addr & 0x3FFF
            inc = 32 if (self.ctrl & 0x04) else 1
            self.vram_addr = (self.vram_addr + inc) & 0x7FFF
            if addr0 < 0x3F00:
                value = self.read_buffer
                self.read_buffer = self.ppu_read(addr0)
                return value
            value = self.ppu_read(addr0)
            self.read_buffer = self.ppu_read(addr0 - 0x1000)
            return value
        return self.read_buffer

    def cpu_write_register(self, addr: int, value: int) -> None:
        value &= 0xFF
        reg = addr & 7
        if reg == 0:  # PPUCTRL
            old = self.ctrl
            self.ctrl = value
            if (not (old & 0x80)) and (value & 0x80) and (self.status & 0x80):
                self.bus.nmi_pending = True
        elif reg == 1:  # PPUMASK
            self.mask = value
        elif reg == 3:  # OAMADDR
            self.oam_addr = value
        elif reg == 4:  # OAMDATA
            self.oam[self.oam_addr] = value
            self.oam_addr = (self.oam_addr + 1) & 0xFF
        elif reg == 5:  # PPUSCROLL
            if self.addr_latch == 0:
                self.scroll_x = value
                self.addr_latch = 1
            else:
                self.scroll_y = value
                self.addr_latch = 0
        elif reg == 6:  # PPUADDR
            if self.addr_latch == 0:
                self.temp_addr = (value & 0x3F) << 8
                self.addr_latch = 1
            else:
                self.temp_addr |= value
                self.vram_addr = self.temp_addr & 0x7FFF
                self.addr_latch = 0
        elif reg == 7:  # PPUDATA
            self.ppu_write(self.vram_addr & 0x3FFF, value)
            inc = 32 if (self.ctrl & 0x04) else 1
            self.vram_addr = (self.vram_addr + inc) & 0x7FFF

    def ppu_read(self, addr: int) -> int:
        addr &= 0x3FFF
        if addr < 0x2000:
            return self.cart.ppu_read(addr)
        if addr < 0x3F00:
            return self.vram[self._mirror_vram_addr(addr)]
        return self.palette_ram[self._palette_index(addr)] & 0x3F

    def ppu_write(self, addr: int, value: int) -> None:
        value &= 0xFF
        addr &= 0x3FFF
        if addr < 0x2000:
            self.cart.ppu_write(addr, value)
        elif addr < 0x3F00:
            self.vram[self._mirror_vram_addr(addr)] = value
        else:
            self.palette_ram[self._palette_index(addr)] = value & 0x3F

    def _mirror_vram_addr(self, addr: int) -> int:
        offset = (addr - 0x2000) & 0x0FFF
        table = offset // 0x400
        inner = offset & 0x03FF
        mir = self.cart.mirroring
        if mir == "vertical":
            table = [0, 1, 0, 1][table]
        elif mir == "horizontal":
            table = [0, 0, 1, 1][table]
        elif mir == "one0":
            table = 0
        elif mir == "one1":
            table = 1
        elif mir == "four":
            table = table
        else:
            table = 0
        return (table * 0x400 + inner) % len(self.vram)

    def _palette_index(self, addr: int) -> int:
        a = (addr - 0x3F00) & 0x1F
        if a in (0x10, 0x14, 0x18, 0x1C):
            a -= 0x10
        return a

    def run_cpu_cycles(self, cpu_cycles: int) -> None:
        cycles = cpu_cycles * 3
        while cycles > 0:
            step = min(cycles, 341 - self.dot)
            if self.sprite0_hit and not (self.status & 0x40):
                hit_y, hit_x = self.sprite0_hit
                if self.scanline == hit_y and self.dot <= hit_x < self.dot + step:
                    if (self.mask & 0x18) and hit_x < 255:
                        self.status |= 0x40
            self.dot += step
            cycles -= step
            if self.dot >= 341:
                old_scanline = self.scanline
                self.dot = 0
                if 0 <= old_scanline <= 239 and (self.mask & 0x18):
                    self.cart.clock_scanline()
                self.scanline += 1
                if self.scanline == 241:
                    self.status |= 0x80
                    self.render_frame()
                    self.frame_counter += 1
                    if self.ctrl & 0x80:
                        self.bus.nmi_pending = True
                elif self.scanline == 261:
                    self.status &= ~(0x80 | 0x40 | 0x20)
                elif self.scanline >= 262:
                    self.scanline = 0

    def render_frame(self) -> None:
        rgb = self.frame_rgb
        opaque = self.bg_opaque
        palette = NES_PALETTE
        universal = self.ppu_read(0x3F00) & 0x3F
        bg_rgb = palette[universal]

        # Start with universal background color.
        r0, g0, b0 = bg_rgb
        for i in range(0, len(rgb), 3):
            rgb[i] = r0
            rgb[i + 1] = g0
            rgb[i + 2] = b0
        opaque[:] = b"\x00" * len(opaque)

        show_bg = bool(self.mask & 0x08)
        show_sprites = bool(self.mask & 0x10)

        if show_bg:
            self._render_background(rgb, opaque, palette)
        self.sprite0_hit = None
        if show_sprites:
            self._render_sprites(rgb, opaque, palette)

    def _render_background(self, rgb: bytearray, opaque: bytearray,
                           palette: List[Tuple[int, int, int]]) -> None:
        base_nt = self.ctrl & 0x03
        pattern_base = 0x1000 if (self.ctrl & 0x10) else 0x0000
        scroll_x = self.scroll_x
        scroll_y = self.scroll_y
        show_left = bool(self.mask & 0x02)

        for y in range(self.HEIGHT):
            # Coarse approximation of the NES scroll/nametable relationship.
            world_y = (((base_nt >> 1) & 1) * 240 + y + scroll_y) % 480
            nt_y_block = world_y // 240
            tile_y = (world_y % 240) // 8
            fine_y = world_y & 7
            for x in range(self.WIDTH):
                if x < 8 and not show_left:
                    continue
                world_x = ((base_nt & 1) * 256 + x + scroll_x) % 512
                nt_x_block = world_x // 256
                nt_index = nt_y_block * 2 + nt_x_block
                tile_x = (world_x % 256) // 8
                fine_x = world_x & 7
                nt_addr = 0x2000 + nt_index * 0x400 + tile_y * 32 + tile_x
                tile = self.ppu_read(nt_addr)
                attr_addr = 0x23C0 + nt_index * 0x400 + (tile_y // 4) * 8 + (tile_x // 4)
                attr = self.ppu_read(attr_addr)
                attr_shift = ((tile_y & 0x02) << 1) | (tile_x & 0x02)
                pal_hi = (attr >> attr_shift) & 0x03
                pat_addr = pattern_base + tile * 16 + fine_y
                lo = self.ppu_read(pat_addr)
                hi = self.ppu_read(pat_addr + 8)
                bit = 7 - fine_x
                color_low = ((lo >> bit) & 1) | (((hi >> bit) & 1) << 1)
                if color_low == 0:
                    continue
                pal_index = self.ppu_read(0x3F00 + pal_hi * 4 + color_low) & 0x3F
                r, g, b = palette[pal_index]
                pix = y * self.WIDTH + x
                p = pix * 3
                rgb[p] = r
                rgb[p + 1] = g
                rgb[p + 2] = b
                opaque[pix] = 1

    def _render_sprites(self, rgb: bytearray, opaque: bytearray,
                        palette: List[Tuple[int, int, int]]) -> None:
        height = 16 if (self.ctrl & 0x20) else 8
        pattern_base_8 = 0x1000 if (self.ctrl & 0x08) else 0x0000
        show_left = bool(self.mask & 0x04)
        found_sprite0: Optional[Tuple[int, int]] = None

        # Draw high-numbered sprites first so low-numbered sprites have priority.
        for i in range(63, -1, -1):
            o = i * 4
            sy = self.oam[o] + 1
            tile = self.oam[o + 1]
            attr = self.oam[o + 2]
            sx = self.oam[o + 3]
            flip_v = bool(attr & 0x80)
            flip_h = bool(attr & 0x40)
            behind_bg = bool(attr & 0x20)
            pal_base = 0x3F10 + (attr & 0x03) * 4

            for row in range(height):
                y = sy + row
                if y < 0 or y >= self.HEIGHT:
                    continue
                fine_y = height - 1 - row if flip_v else row
                if height == 16:
                    table = (tile & 1) * 0x1000
                    tile_index = tile & 0xFE
                    if fine_y >= 8:
                        tile_index += 1
                        fine_y -= 8
                    pat_addr = table + tile_index * 16 + fine_y
                else:
                    pat_addr = pattern_base_8 + tile * 16 + fine_y
                lo = self.ppu_read(pat_addr)
                hi = self.ppu_read(pat_addr + 8)
                for col in range(8):
                    x = sx + col
                    if x < 0 or x >= self.WIDTH:
                        continue
                    if x < 8 and not show_left:
                        continue
                    bit = col if flip_h else (7 - col)
                    color_low = ((lo >> bit) & 1) | (((hi >> bit) & 1) << 1)
                    if color_low == 0:
                        continue
                    pix = y * self.WIDTH + x
                    if i == 0 and opaque[pix] and found_sprite0 is None and x < 255:
                        found_sprite0 = (y, x)
                    if behind_bg and opaque[pix]:
                        continue
                    pal_index = self.ppu_read(pal_base + color_low) & 0x3F
                    r, g, b = palette[pal_index]
                    p = pix * 3
                    rgb[p] = r
                    rgb[p + 1] = g
                    rgb[p + 2] = b

        self.sprite0_hit = found_sprite0


# ---------------------------------------------------------------------------
# CPU bus
# ---------------------------------------------------------------------------

class Bus:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.ram = bytearray(0x800)
        self.ppu: Optional[PPU] = None
        self.controllers = [Controller(), Controller()]
        self.nmi_pending = False
        self.dma_cycles = 0
        self.open_bus = 0

    def read(self, addr: int) -> int:
        addr &= 0xFFFF
        if addr < 0x2000:
            value = self.ram[addr & 0x07FF]
        elif addr < 0x4000:
            value = self.ppu.cpu_read_register(0x2000 + (addr & 7)) if self.ppu else 0
        elif addr == 0x4016:
            value = self.controllers[0].read()
        elif addr == 0x4017:
            value = self.controllers[1].read()
        elif addr == 0x4015:
            value = 0
        elif addr < 0x4020:
            value = 0
        else:
            value = self.cart.cpu_read(addr)
        self.open_bus = value & 0xFF
        return self.open_bus

    def write(self, addr: int, value: int) -> None:
        addr &= 0xFFFF
        value &= 0xFF
        self.open_bus = value
        if addr < 0x2000:
            self.ram[addr & 0x07FF] = value
        elif addr < 0x4000:
            if self.ppu:
                self.ppu.cpu_write_register(0x2000 + (addr & 7), value)
        elif addr == 0x4014:
            self._oam_dma(value)
        elif addr == 0x4016:
            self.controllers[0].write_strobe(value)
            self.controllers[1].write_strobe(value)
        elif addr < 0x4020:
            pass  # APU and test registers are stubbed.
        else:
            self.cart.cpu_write(addr, value)

    def _oam_dma(self, page: int) -> None:
        if not self.ppu:
            return
        base = (page & 0xFF) << 8
        start = self.ppu.oam_addr
        for i in range(256):
            self.ppu.oam[(start + i) & 0xFF] = self.read(base + i)
        self.dma_cycles += 513

    def consume_dma_cycles(self) -> int:
        c = self.dma_cycles
        self.dma_cycles = 0
        return c

    def consume_nmi(self) -> bool:
        if self.nmi_pending:
            self.nmi_pending = False
            return True
        return False

    def irq_pending(self) -> bool:
        return bool(self.cart.irq_pending)


# ---------------------------------------------------------------------------
# 6502 CPU core
# ---------------------------------------------------------------------------

C_FLAG = 0x01
Z_FLAG = 0x02
I_FLAG = 0x04
D_FLAG = 0x08
B_FLAG = 0x10
U_FLAG = 0x20
V_FLAG = 0x40
N_FLAG = 0x80

# inst, addressing mode, base cycles, page-cross extra flag
OPCODES: Dict[int, Tuple[str, str, int, int]] = {
    # Load/store
    0xA9: ("LDA", "imm", 2, 0), 0xA5: ("LDA", "zp", 3, 0), 0xB5: ("LDA", "zpx", 4, 0),
    0xAD: ("LDA", "abs", 4, 0), 0xBD: ("LDA", "absx", 4, 1), 0xB9: ("LDA", "absy", 4, 1),
    0xA1: ("LDA", "indx", 6, 0), 0xB1: ("LDA", "indy", 5, 1),
    0xA2: ("LDX", "imm", 2, 0), 0xA6: ("LDX", "zp", 3, 0), 0xB6: ("LDX", "zpy", 4, 0),
    0xAE: ("LDX", "abs", 4, 0), 0xBE: ("LDX", "absy", 4, 1),
    0xA0: ("LDY", "imm", 2, 0), 0xA4: ("LDY", "zp", 3, 0), 0xB4: ("LDY", "zpx", 4, 0),
    0xAC: ("LDY", "abs", 4, 0), 0xBC: ("LDY", "absx", 4, 1),
    0x85: ("STA", "zp", 3, 0), 0x95: ("STA", "zpx", 4, 0), 0x8D: ("STA", "abs", 4, 0),
    0x9D: ("STA", "absx", 5, 0), 0x99: ("STA", "absy", 5, 0), 0x81: ("STA", "indx", 6, 0),
    0x91: ("STA", "indy", 6, 0),
    0x86: ("STX", "zp", 3, 0), 0x96: ("STX", "zpy", 4, 0), 0x8E: ("STX", "abs", 4, 0),
    0x84: ("STY", "zp", 3, 0), 0x94: ("STY", "zpx", 4, 0), 0x8C: ("STY", "abs", 4, 0),

    # Arithmetic / logic
    0x69: ("ADC", "imm", 2, 0), 0x65: ("ADC", "zp", 3, 0), 0x75: ("ADC", "zpx", 4, 0),
    0x6D: ("ADC", "abs", 4, 0), 0x7D: ("ADC", "absx", 4, 1), 0x79: ("ADC", "absy", 4, 1),
    0x61: ("ADC", "indx", 6, 0), 0x71: ("ADC", "indy", 5, 1),
    0xE9: ("SBC", "imm", 2, 0), 0xE5: ("SBC", "zp", 3, 0), 0xF5: ("SBC", "zpx", 4, 0),
    0xED: ("SBC", "abs", 4, 0), 0xFD: ("SBC", "absx", 4, 1), 0xF9: ("SBC", "absy", 4, 1),
    0xE1: ("SBC", "indx", 6, 0), 0xF1: ("SBC", "indy", 5, 1), 0xEB: ("SBC", "imm", 2, 0),
    0x29: ("AND", "imm", 2, 0), 0x25: ("AND", "zp", 3, 0), 0x35: ("AND", "zpx", 4, 0),
    0x2D: ("AND", "abs", 4, 0), 0x3D: ("AND", "absx", 4, 1), 0x39: ("AND", "absy", 4, 1),
    0x21: ("AND", "indx", 6, 0), 0x31: ("AND", "indy", 5, 1),
    0x09: ("ORA", "imm", 2, 0), 0x05: ("ORA", "zp", 3, 0), 0x15: ("ORA", "zpx", 4, 0),
    0x0D: ("ORA", "abs", 4, 0), 0x1D: ("ORA", "absx", 4, 1), 0x19: ("ORA", "absy", 4, 1),
    0x01: ("ORA", "indx", 6, 0), 0x11: ("ORA", "indy", 5, 1),
    0x49: ("EOR", "imm", 2, 0), 0x45: ("EOR", "zp", 3, 0), 0x55: ("EOR", "zpx", 4, 0),
    0x4D: ("EOR", "abs", 4, 0), 0x5D: ("EOR", "absx", 4, 1), 0x59: ("EOR", "absy", 4, 1),
    0x41: ("EOR", "indx", 6, 0), 0x51: ("EOR", "indy", 5, 1),
    0xC9: ("CMP", "imm", 2, 0), 0xC5: ("CMP", "zp", 3, 0), 0xD5: ("CMP", "zpx", 4, 0),
    0xCD: ("CMP", "abs", 4, 0), 0xDD: ("CMP", "absx", 4, 1), 0xD9: ("CMP", "absy", 4, 1),
    0xC1: ("CMP", "indx", 6, 0), 0xD1: ("CMP", "indy", 5, 1),
    0xE0: ("CPX", "imm", 2, 0), 0xE4: ("CPX", "zp", 3, 0), 0xEC: ("CPX", "abs", 4, 0),
    0xC0: ("CPY", "imm", 2, 0), 0xC4: ("CPY", "zp", 3, 0), 0xCC: ("CPY", "abs", 4, 0),
    0x24: ("BIT", "zp", 3, 0), 0x2C: ("BIT", "abs", 4, 0),

    # Shifts / increments
    0x0A: ("ASL", "acc", 2, 0), 0x06: ("ASL", "zp", 5, 0), 0x16: ("ASL", "zpx", 6, 0),
    0x0E: ("ASL", "abs", 6, 0), 0x1E: ("ASL", "absx", 7, 0),
    0x4A: ("LSR", "acc", 2, 0), 0x46: ("LSR", "zp", 5, 0), 0x56: ("LSR", "zpx", 6, 0),
    0x4E: ("LSR", "abs", 6, 0), 0x5E: ("LSR", "absx", 7, 0),
    0x2A: ("ROL", "acc", 2, 0), 0x26: ("ROL", "zp", 5, 0), 0x36: ("ROL", "zpx", 6, 0),
    0x2E: ("ROL", "abs", 6, 0), 0x3E: ("ROL", "absx", 7, 0),
    0x6A: ("ROR", "acc", 2, 0), 0x66: ("ROR", "zp", 5, 0), 0x76: ("ROR", "zpx", 6, 0),
    0x6E: ("ROR", "abs", 6, 0), 0x7E: ("ROR", "absx", 7, 0),
    0xE6: ("INC", "zp", 5, 0), 0xF6: ("INC", "zpx", 6, 0), 0xEE: ("INC", "abs", 6, 0),
    0xFE: ("INC", "absx", 7, 0),
    0xC6: ("DEC", "zp", 5, 0), 0xD6: ("DEC", "zpx", 6, 0), 0xCE: ("DEC", "abs", 6, 0),
    0xDE: ("DEC", "absx", 7, 0),

    # Jumps / branches
    0x4C: ("JMP", "abs", 3, 0), 0x6C: ("JMP", "ind", 5, 0), 0x20: ("JSR", "abs", 6, 0),
    0x60: ("RTS", "impl", 6, 0), 0x40: ("RTI", "impl", 6, 0), 0x00: ("BRK", "impl", 7, 0),
    0x10: ("BPL", "rel", 2, 0), 0x30: ("BMI", "rel", 2, 0), 0x50: ("BVC", "rel", 2, 0),
    0x70: ("BVS", "rel", 2, 0), 0x90: ("BCC", "rel", 2, 0), 0xB0: ("BCS", "rel", 2, 0),
    0xD0: ("BNE", "rel", 2, 0), 0xF0: ("BEQ", "rel", 2, 0),

    # Stack / transfer / flags
    0x48: ("PHA", "impl", 3, 0), 0x68: ("PLA", "impl", 4, 0), 0x08: ("PHP", "impl", 3, 0),
    0x28: ("PLP", "impl", 4, 0),
    0xAA: ("TAX", "impl", 2, 0), 0x8A: ("TXA", "impl", 2, 0), 0xA8: ("TAY", "impl", 2, 0),
    0x98: ("TYA", "impl", 2, 0), 0xBA: ("TSX", "impl", 2, 0), 0x9A: ("TXS", "impl", 2, 0),
    0xE8: ("INX", "impl", 2, 0), 0xC8: ("INY", "impl", 2, 0), 0xCA: ("DEX", "impl", 2, 0),
    0x88: ("DEY", "impl", 2, 0),
    0x18: ("CLC", "impl", 2, 0), 0x38: ("SEC", "impl", 2, 0), 0x58: ("CLI", "impl", 2, 0),
    0x78: ("SEI", "impl", 2, 0), 0xB8: ("CLV", "impl", 2, 0), 0xD8: ("CLD", "impl", 2, 0),
    0xF8: ("SED", "impl", 2, 0), 0xEA: ("NOP", "impl", 2, 0),
}

# Common undocumented opcodes. They are included because some homebrew and
# test ROMs use them; many commercial games do not need them.
UNOFFICIAL_OPCODES: Dict[int, Tuple[str, str, int, int]] = {
    # NOP variants
    0x1A: ("NOP", "impl", 2, 0), 0x3A: ("NOP", "impl", 2, 0), 0x5A: ("NOP", "impl", 2, 0),
    0x7A: ("NOP", "impl", 2, 0), 0xDA: ("NOP", "impl", 2, 0), 0xFA: ("NOP", "impl", 2, 0),
    0x80: ("NOP", "imm", 2, 0), 0x82: ("NOP", "imm", 2, 0), 0x89: ("NOP", "imm", 2, 0),
    0xC2: ("NOP", "imm", 2, 0), 0xE2: ("NOP", "imm", 2, 0),
    0x04: ("NOP", "zp", 3, 0), 0x44: ("NOP", "zp", 3, 0), 0x64: ("NOP", "zp", 3, 0),
    0x14: ("NOP", "zpx", 4, 0), 0x34: ("NOP", "zpx", 4, 0), 0x54: ("NOP", "zpx", 4, 0),
    0x74: ("NOP", "zpx", 4, 0), 0xD4: ("NOP", "zpx", 4, 0), 0xF4: ("NOP", "zpx", 4, 0),
    0x0C: ("NOP", "abs", 4, 0),
    0x1C: ("NOP", "absx", 4, 1), 0x3C: ("NOP", "absx", 4, 1), 0x5C: ("NOP", "absx", 4, 1),
    0x7C: ("NOP", "absx", 4, 1), 0xDC: ("NOP", "absx", 4, 1), 0xFC: ("NOP", "absx", 4, 1),

    # Read-like unofficials
    0xA7: ("LAX", "zp", 3, 0), 0xB7: ("LAX", "zpy", 4, 0), 0xAF: ("LAX", "abs", 4, 0),
    0xBF: ("LAX", "absy", 4, 1), 0xA3: ("LAX", "indx", 6, 0), 0xB3: ("LAX", "indy", 5, 1),
    0x87: ("SAX", "zp", 3, 0), 0x97: ("SAX", "zpy", 4, 0), 0x8F: ("SAX", "abs", 4, 0),
    0x83: ("SAX", "indx", 6, 0),

    # Read-modify-write unofficials
    0xC7: ("DCP", "zp", 5, 0), 0xD7: ("DCP", "zpx", 6, 0), 0xCF: ("DCP", "abs", 6, 0),
    0xDF: ("DCP", "absx", 7, 0), 0xDB: ("DCP", "absy", 7, 0), 0xC3: ("DCP", "indx", 8, 0),
    0xD3: ("DCP", "indy", 8, 0),
    0xE7: ("ISC", "zp", 5, 0), 0xF7: ("ISC", "zpx", 6, 0), 0xEF: ("ISC", "abs", 6, 0),
    0xFF: ("ISC", "absx", 7, 0), 0xFB: ("ISC", "absy", 7, 0), 0xE3: ("ISC", "indx", 8, 0),
    0xF3: ("ISC", "indy", 8, 0),
    0x07: ("SLO", "zp", 5, 0), 0x17: ("SLO", "zpx", 6, 0), 0x0F: ("SLO", "abs", 6, 0),
    0x1F: ("SLO", "absx", 7, 0), 0x1B: ("SLO", "absy", 7, 0), 0x03: ("SLO", "indx", 8, 0),
    0x13: ("SLO", "indy", 8, 0),
    0x27: ("RLA", "zp", 5, 0), 0x37: ("RLA", "zpx", 6, 0), 0x2F: ("RLA", "abs", 6, 0),
    0x3F: ("RLA", "absx", 7, 0), 0x3B: ("RLA", "absy", 7, 0), 0x23: ("RLA", "indx", 8, 0),
    0x33: ("RLA", "indy", 8, 0),
    0x47: ("SRE", "zp", 5, 0), 0x57: ("SRE", "zpx", 6, 0), 0x4F: ("SRE", "abs", 6, 0),
    0x5F: ("SRE", "absx", 7, 0), 0x5B: ("SRE", "absy", 7, 0), 0x43: ("SRE", "indx", 8, 0),
    0x53: ("SRE", "indy", 8, 0),
    0x67: ("RRA", "zp", 5, 0), 0x77: ("RRA", "zpx", 6, 0), 0x6F: ("RRA", "abs", 6, 0),
    0x7F: ("RRA", "absx", 7, 0), 0x7B: ("RRA", "absy", 7, 0), 0x63: ("RRA", "indx", 8, 0),
    0x73: ("RRA", "indy", 8, 0),

    # Misc immediate unofficials
    0x0B: ("ANC", "imm", 2, 0), 0x2B: ("ANC", "imm", 2, 0), 0x4B: ("ALR", "imm", 2, 0),
    0x6B: ("ARR", "imm", 2, 0), 0xCB: ("AXS", "imm", 2, 0),
}


class CPU:
    def __init__(self, bus: Bus) -> None:
        self.bus = bus
        self.a = 0
        self.x = 0
        self.y = 0
        self.sp = 0xFD
        self.pc = 0
        self.p = I_FLAG | U_FLAG
        self.cycles = 0
        self.illegal_op_count = 0
        self.reset()

    def reset(self) -> None:
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.p = I_FLAG | U_FLAG
        self.pc = self.read16(0xFFFC)
        self.cycles = 7

    def read(self, addr: int) -> int:
        return self.bus.read(addr)

    def write(self, addr: int, value: int) -> None:
        self.bus.write(addr, value)

    def read16(self, addr: int) -> int:
        lo = self.read(addr)
        hi = self.read((addr + 1) & 0xFFFF)
        return lo | (hi << 8)

    def fetch8(self) -> int:
        v = self.read(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        return v

    def fetch16(self) -> int:
        lo = self.fetch8()
        hi = self.fetch8()
        return lo | (hi << 8)

    def push(self, value: int) -> None:
        self.write(0x0100 | self.sp, value)
        self.sp = (self.sp - 1) & 0xFF

    def pop(self) -> int:
        self.sp = (self.sp + 1) & 0xFF
        return self.read(0x0100 | self.sp)

    def set_flag(self, flag: int, value: bool) -> None:
        if value:
            self.p |= flag
        else:
            self.p &= ~flag
        self.p |= U_FLAG

    def get_flag(self, flag: int) -> bool:
        return bool(self.p & flag)

    def set_zn(self, value: int) -> None:
        value &= 0xFF
        self.set_flag(Z_FLAG, value == 0)
        self.set_flag(N_FLAG, bool(value & 0x80))

    def addr(self, mode: str) -> Tuple[int, bool]:
        if mode == "imm":
            a = self.pc
            self.pc = (self.pc + 1) & 0xFFFF
            return a, False
        if mode == "zp":
            return self.fetch8(), False
        if mode == "zpx":
            return (self.fetch8() + self.x) & 0xFF, False
        if mode == "zpy":
            return (self.fetch8() + self.y) & 0xFF, False
        if mode == "abs":
            return self.fetch16(), False
        if mode == "absx":
            base = self.fetch16()
            a = (base + self.x) & 0xFFFF
            return a, (base & 0xFF00) != (a & 0xFF00)
        if mode == "absy":
            base = self.fetch16()
            a = (base + self.y) & 0xFFFF
            return a, (base & 0xFF00) != (a & 0xFF00)
        if mode == "indx":
            zp = (self.fetch8() + self.x) & 0xFF
            lo = self.read(zp)
            hi = self.read((zp + 1) & 0xFF)
            return lo | (hi << 8), False
        if mode == "indy":
            zp = self.fetch8()
            lo = self.read(zp)
            hi = self.read((zp + 1) & 0xFF)
            base = lo | (hi << 8)
            a = (base + self.y) & 0xFFFF
            return a, (base & 0xFF00) != (a & 0xFF00)
        if mode == "ind":
            ptr = self.fetch16()
            lo = self.read(ptr)
            hi = self.read((ptr & 0xFF00) | ((ptr + 1) & 0x00FF))  # 6502 JMP bug
            return lo | (hi << 8), False
        raise RuntimeError(f"bad addressing mode {mode}")

    def adc(self, value: int) -> None:
        value &= 0xFF
        carry = 1 if self.get_flag(C_FLAG) else 0
        total = self.a + value + carry
        result = total & 0xFF
        self.set_flag(C_FLAG, total > 0xFF)
        self.set_flag(V_FLAG, bool((~(self.a ^ value) & (self.a ^ result) & 0x80)))
        self.a = result
        self.set_zn(self.a)

    def compare(self, reg: int, value: int) -> None:
        temp = (reg - value) & 0x1FF
        self.set_flag(C_FLAG, reg >= value)
        self.set_zn(temp & 0xFF)

    def interrupt(self, vector: int, brk: bool = False) -> None:
        self.push((self.pc >> 8) & 0xFF)
        self.push(self.pc & 0xFF)
        flags = self.p | U_FLAG
        if brk:
            flags |= B_FLAG
        else:
            flags &= ~B_FLAG
        self.push(flags)
        self.set_flag(I_FLAG, True)
        self.pc = self.read16(vector)

    def step(self) -> int:
        if self.bus.consume_nmi():
            self.interrupt(0xFFFA, False)
            self.cycles += 7
            return 7
        if self.bus.irq_pending() and not self.get_flag(I_FLAG):
            self.interrupt(0xFFFE, False)
            self.cycles += 7
            return 7

        opcode = self.fetch8()
        info = OPCODES.get(opcode) or UNOFFICIAL_OPCODES.get(opcode)
        if info is None:
            # Unknown illegal opcode. Treat as a two-cycle NOP to avoid crashing
            # the GUI; ROMs that depend on it may not run correctly.
            self.illegal_op_count += 1
            cycles = 2
            self.cycles += cycles
            return cycles

        inst, mode, cycles, page_extra = info
        crossed = False

        if inst == "NOP":
            if mode != "impl":
                _, crossed = self.addr(mode)
            if page_extra and crossed:
                cycles += 1

        elif inst in ("LDA", "LDX", "LDY", "ADC", "SBC", "AND", "ORA", "EOR", "CMP", "CPX", "CPY", "BIT", "LAX"):
            a, crossed = self.addr(mode)
            value = self.read(a)
            if page_extra and crossed:
                cycles += 1
            if inst == "LDA":
                self.a = value; self.set_zn(self.a)
            elif inst == "LDX":
                self.x = value; self.set_zn(self.x)
            elif inst == "LDY":
                self.y = value; self.set_zn(self.y)
            elif inst == "ADC":
                self.adc(value)
            elif inst == "SBC":
                self.adc(value ^ 0xFF)
            elif inst == "AND":
                self.a &= value; self.set_zn(self.a)
            elif inst == "ORA":
                self.a |= value; self.set_zn(self.a)
            elif inst == "EOR":
                self.a ^= value; self.set_zn(self.a)
            elif inst == "CMP":
                self.compare(self.a, value)
            elif inst == "CPX":
                self.compare(self.x, value)
            elif inst == "CPY":
                self.compare(self.y, value)
            elif inst == "BIT":
                self.set_flag(Z_FLAG, (self.a & value) == 0)
                self.set_flag(V_FLAG, bool(value & 0x40))
                self.set_flag(N_FLAG, bool(value & 0x80))
            elif inst == "LAX":
                self.a = self.x = value; self.set_zn(value)

        elif inst in ("STA", "STX", "STY", "SAX"):
            a, _ = self.addr(mode)
            if inst == "STA":
                self.write(a, self.a)
            elif inst == "STX":
                self.write(a, self.x)
            elif inst == "STY":
                self.write(a, self.y)
            else:
                self.write(a, self.a & self.x)

        elif inst in ("ASL", "LSR", "ROL", "ROR", "INC", "DEC", "DCP", "ISC", "SLO", "RLA", "SRE", "RRA"):
            if mode == "acc":
                old = self.a
                new = self._shift_value(inst, old)
                self.a = new
            else:
                a, _ = self.addr(mode)
                old = self.read(a)
                if inst in ("INC", "DEC"):
                    new = (old + (1 if inst == "INC" else -1)) & 0xFF
                    self.write(a, new)
                    self.set_zn(new)
                elif inst == "DCP":
                    new = (old - 1) & 0xFF
                    self.write(a, new)
                    self.compare(self.a, new)
                elif inst == "ISC":
                    new = (old + 1) & 0xFF
                    self.write(a, new)
                    self.adc(new ^ 0xFF)
                elif inst == "SLO":
                    new = self._shift_value("ASL", old)
                    self.write(a, new)
                    self.a |= new; self.set_zn(self.a)
                elif inst == "RLA":
                    new = self._shift_value("ROL", old)
                    self.write(a, new)
                    self.a &= new; self.set_zn(self.a)
                elif inst == "SRE":
                    new = self._shift_value("LSR", old)
                    self.write(a, new)
                    self.a ^= new; self.set_zn(self.a)
                elif inst == "RRA":
                    new = self._shift_value("ROR", old)
                    self.write(a, new)
                    self.adc(new)
                else:
                    new = self._shift_value(inst, old)
                    self.write(a, new)

        elif inst == "JMP":
            a, _ = self.addr(mode)
            self.pc = a
        elif inst == "JSR":
            target = self.fetch16()
            ret = (self.pc - 1) & 0xFFFF
            self.push((ret >> 8) & 0xFF)
            self.push(ret & 0xFF)
            self.pc = target
        elif inst == "RTS":
            lo = self.pop()
            hi = self.pop()
            self.pc = ((lo | (hi << 8)) + 1) & 0xFFFF
        elif inst == "RTI":
            self.p = (self.pop() | U_FLAG) & 0xFF
            lo = self.pop()
            hi = self.pop()
            self.pc = lo | (hi << 8)
        elif inst == "BRK":
            self.pc = (self.pc + 1) & 0xFFFF
            self.interrupt(0xFFFE, True)

        elif inst in ("BPL", "BMI", "BVC", "BVS", "BCC", "BCS", "BNE", "BEQ"):
            offset = self.fetch8()
            if offset & 0x80:
                offset -= 0x100
            cond = {
                "BPL": not self.get_flag(N_FLAG),
                "BMI": self.get_flag(N_FLAG),
                "BVC": not self.get_flag(V_FLAG),
                "BVS": self.get_flag(V_FLAG),
                "BCC": not self.get_flag(C_FLAG),
                "BCS": self.get_flag(C_FLAG),
                "BNE": not self.get_flag(Z_FLAG),
                "BEQ": self.get_flag(Z_FLAG),
            }[inst]
            if cond:
                old_pc = self.pc
                self.pc = (self.pc + offset) & 0xFFFF
                cycles += 1
                if (old_pc & 0xFF00) != (self.pc & 0xFF00):
                    cycles += 1

        elif inst == "PHA":
            self.push(self.a)
        elif inst == "PLA":
            self.a = self.pop(); self.set_zn(self.a)
        elif inst == "PHP":
            self.push(self.p | B_FLAG | U_FLAG)
        elif inst == "PLP":
            self.p = (self.pop() | U_FLAG) & 0xFF
        elif inst == "TAX":
            self.x = self.a; self.set_zn(self.x)
        elif inst == "TXA":
            self.a = self.x; self.set_zn(self.a)
        elif inst == "TAY":
            self.y = self.a; self.set_zn(self.y)
        elif inst == "TYA":
            self.a = self.y; self.set_zn(self.a)
        elif inst == "TSX":
            self.x = self.sp; self.set_zn(self.x)
        elif inst == "TXS":
            self.sp = self.x
        elif inst == "INX":
            self.x = (self.x + 1) & 0xFF; self.set_zn(self.x)
        elif inst == "INY":
            self.y = (self.y + 1) & 0xFF; self.set_zn(self.y)
        elif inst == "DEX":
            self.x = (self.x - 1) & 0xFF; self.set_zn(self.x)
        elif inst == "DEY":
            self.y = (self.y - 1) & 0xFF; self.set_zn(self.y)
        elif inst == "CLC":
            self.set_flag(C_FLAG, False)
        elif inst == "SEC":
            self.set_flag(C_FLAG, True)
        elif inst == "CLI":
            self.set_flag(I_FLAG, False)
        elif inst == "SEI":
            self.set_flag(I_FLAG, True)
        elif inst == "CLV":
            self.set_flag(V_FLAG, False)
        elif inst == "CLD":
            self.set_flag(D_FLAG, False)
        elif inst == "SED":
            self.set_flag(D_FLAG, True)

        elif inst == "ANC":
            a, _ = self.addr(mode)
            self.a &= self.read(a)
            self.set_zn(self.a)
            self.set_flag(C_FLAG, bool(self.a & 0x80))
        elif inst == "ALR":
            a, _ = self.addr(mode)
            self.a &= self.read(a)
            self.set_flag(C_FLAG, bool(self.a & 1))
            self.a = (self.a >> 1) & 0xFF
            self.set_zn(self.a)
        elif inst == "ARR":
            a, _ = self.addr(mode)
            self.a &= self.read(a)
            carry_in = 0x80 if self.get_flag(C_FLAG) else 0
            self.a = ((self.a >> 1) | carry_in) & 0xFF
            self.set_zn(self.a)
            self.set_flag(C_FLAG, bool(self.a & 0x40))
            self.set_flag(V_FLAG, bool(((self.a >> 6) ^ (self.a >> 5)) & 1))
        elif inst == "AXS":
            a, _ = self.addr(mode)
            value = self.read(a)
            temp = (self.a & self.x) - value
            self.set_flag(C_FLAG, temp >= 0)
            self.x = temp & 0xFF
            self.set_zn(self.x)

        extra = self.bus.consume_dma_cycles()
        cycles += extra
        self.cycles += cycles
        return cycles

    def _shift_value(self, inst: str, value: int) -> int:
        value &= 0xFF
        if inst == "ASL":
            self.set_flag(C_FLAG, bool(value & 0x80))
            result = (value << 1) & 0xFF
        elif inst == "LSR":
            self.set_flag(C_FLAG, bool(value & 0x01))
            result = (value >> 1) & 0xFF
        elif inst == "ROL":
            carry = 1 if self.get_flag(C_FLAG) else 0
            self.set_flag(C_FLAG, bool(value & 0x80))
            result = ((value << 1) | carry) & 0xFF
        elif inst == "ROR":
            carry = 0x80 if self.get_flag(C_FLAG) else 0
            self.set_flag(C_FLAG, bool(value & 0x01))
            result = ((value >> 1) | carry) & 0xFF
        else:
            raise RuntimeError("bad shift")
        self.set_zn(result)
        return result


# ---------------------------------------------------------------------------
# Complete NES machine wrapper
# ---------------------------------------------------------------------------

class NES:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.bus = Bus(cart)
        self.ppu = PPU(cart, self.bus)
        self.bus.ppu = self.ppu
        self.cpu = CPU(self.bus)

    @classmethod
    def from_bytes(cls, data: bytes, name: str = "<memory>") -> "NES":
        return cls(Cartridge(data, name))

    @classmethod
    def from_file(cls, path: str) -> "NES":
        return cls(Cartridge.from_file(path))

    def reset(self) -> None:
        # Preserve controller state but reset CPU/PPU/bus timing.
        controllers = self.bus.controllers
        self.bus = Bus(self.cart)
        self.bus.controllers = controllers
        self.ppu = PPU(self.cart, self.bus)
        self.bus.ppu = self.ppu
        self.cpu = CPU(self.bus)

    def run_until_next_frame(self, max_cpu_cycles: int = 80000) -> int:
        target = self.ppu.frame_counter + 1
        used = 0
        while self.ppu.frame_counter < target and used < max_cpu_cycles:
            cycles = self.cpu.step()
            used += cycles
            self.ppu.run_cpu_cycles(cycles)
        return used


# ---------------------------------------------------------------------------
# Built-in tiny legal NROM demo ROM
# ---------------------------------------------------------------------------

class TinyAssembler:
    def __init__(self, origin: int) -> None:
        self.origin = origin
        self.pc = origin
        self.code = bytearray()
        self.labels: Dict[str, int] = {}
        self.patches: List[Tuple[str, int, str, int]] = []

    def label(self, name: str) -> None:
        self.labels[name] = self.pc

    def emit(self, *values: int) -> None:
        for v in values:
            self.code.append(v & 0xFF)
            self.pc += 1

    def abs_operand(self, target) -> None:
        if isinstance(target, str):
            pos = len(self.code)
            self.emit(0, 0)
            self.patches.append(("abs", pos, target, 0))
        else:
            self.emit(target & 0xFF, (target >> 8) & 0xFF)

    def branch(self, opcode: int, target: str) -> None:
        self.emit(opcode, 0)
        # The base for relative addressing is PC after the operand.
        self.patches.append(("rel", len(self.code) - 1, target, self.pc))

    def patch(self) -> None:
        for kind, pos, label, base in self.patches:
            if label not in self.labels:
                raise CartridgeError(f"demo assembler missing label {label}")
            target = self.labels[label]
            if kind == "abs":
                self.code[pos] = target & 0xFF
                self.code[pos + 1] = (target >> 8) & 0xFF
            elif kind == "rel":
                off = target - base
                if not -128 <= off <= 127:
                    raise CartridgeError(f"branch to {label} is out of range")
                self.code[pos] = off & 0xFF

    # Small opcode helpers used by the demo.
    def LDAi(self, v): self.emit(0xA9, v)
    def LDXi(self, v): self.emit(0xA2, v)
    def LDYi(self, v): self.emit(0xA0, v)
    def LDAabs(self, a): self.emit(0xAD); self.abs_operand(a)
    def LDAabsX(self, a): self.emit(0xBD); self.abs_operand(a)
    def STAabs(self, a): self.emit(0x8D); self.abs_operand(a)
    def STAabsX(self, a): self.emit(0x9D); self.abs_operand(a)
    def STXabs(self, a): self.emit(0x8E); self.abs_operand(a)
    def STYabs(self, a): self.emit(0x8C); self.abs_operand(a)
    def STAzp(self, a): self.emit(0x85, a)
    def LDAzp(self, a): self.emit(0xA5, a)
    def INCzp(self, a): self.emit(0xE6, a)
    def DECzp(self, a): self.emit(0xC6, a)
    def CPXi(self, v): self.emit(0xE0, v)
    def ANDi(self, v): self.emit(0x29, v)
    def JMP(self, target): self.emit(0x4C); self.abs_operand(target)
    def BITabs(self, a): self.emit(0x2C); self.abs_operand(a)
    def BPL(self, target): self.branch(0x10, target)
    def BNE(self, target): self.branch(0xD0, target)
    def BEQ(self, target): self.branch(0xF0, target)
    def PHA(self): self.emit(0x48)
    def PLA(self): self.emit(0x68)
    def TXA(self): self.emit(0x8A)
    def TAX(self): self.emit(0xAA)
    def TYA(self): self.emit(0x98)
    def TAY(self): self.emit(0xA8)
    def TXS(self): self.emit(0x9A)
    def INX(self): self.emit(0xE8)
    def INY(self): self.emit(0xC8)
    def DEX(self): self.emit(0xCA)
    def SEI(self): self.emit(0x78)
    def CLD(self): self.emit(0xD8)
    def RTI(self): self.emit(0x40)


def make_builtin_demo_rom() -> bytes:
    """Create a tiny legal iNES ROM in memory: move a sprite with arrow keys."""
    PRG_ORG = 0x8000
    PLAYER_X = 0x00
    PLAYER_Y = 0x01

    a = TinyAssembler(PRG_ORG)
    a.label("reset")
    a.SEI()
    a.CLD()
    a.LDXi(0x40); a.STXabs(0x4017)
    a.LDXi(0xFF); a.TXS()
    a.INX()  # X = 0
    a.STXabs(0x2000); a.STXabs(0x2001); a.STXabs(0x4010)

    a.label("wait_vblank")
    a.BITabs(0x2002)
    a.BPL("wait_vblank")

    # Hide all sprites initially.
    a.LDAi(0x80)
    a.LDXi(0x00)
    a.label("clear_oam")
    a.STAabsX(0x0200)
    a.INX()
    a.BNE("clear_oam")

    a.LDAi(0x78); a.STAzp(PLAYER_X)
    a.LDAi(0x70); a.STAzp(PLAYER_Y)

    # Palettes.
    a.LDAi(0x3F); a.STAabs(0x2006)
    a.LDAi(0x00); a.STAabs(0x2006)
    a.LDXi(0x00)
    a.label("pal_loop")
    a.LDAabsX("palettes")
    a.STAabs(0x2007)
    a.INX()
    a.CPXi(0x20)
    a.BNE("pal_loop")

    # Clear nametable and attributes.
    a.LDAi(0x20); a.STAabs(0x2006)
    a.LDAi(0x00); a.STAabs(0x2006)
    a.LDAi(0x00)
    a.LDXi(0x04)
    a.LDYi(0x00)
    a.label("nt_loop")
    a.STAabs(0x2007)
    a.INY()
    a.BNE("nt_loop")
    a.DEX()
    a.BNE("nt_loop")

    # Reset scroll and turn on NMI + sprites/background.
    a.LDAi(0x00); a.STAabs(0x2005); a.STAabs(0x2005)
    a.LDAi(0x80); a.STAabs(0x2000)
    a.LDAi(0x1E); a.STAabs(0x2001)
    a.label("forever")
    a.JMP("forever")

    # NMI: move sprite, upload OAM through DMA.
    a.label("nmi")
    a.PHA(); a.TXA(); a.PHA(); a.TYA(); a.PHA()

    a.LDAzp(PLAYER_Y); a.STAabs(0x0200)
    a.LDAi(0x01); a.STAabs(0x0201)
    a.LDAi(0x00); a.STAabs(0x0202)
    a.LDAzp(PLAYER_X); a.STAabs(0x0203)

    # Strobe controller and discard A/B/Select/Start.
    a.LDAi(0x01); a.STAabs(0x4016)
    a.LDAi(0x00); a.STAabs(0x4016)
    for _ in range(4):
        a.LDAabs(0x4016)

    # Up.
    a.LDAabs(0x4016); a.ANDi(0x01); a.BEQ("no_up"); a.DECzp(PLAYER_Y); a.label("no_up")
    # Down.
    a.LDAabs(0x4016); a.ANDi(0x01); a.BEQ("no_down"); a.INCzp(PLAYER_Y); a.label("no_down")
    # Left.
    a.LDAabs(0x4016); a.ANDi(0x01); a.BEQ("no_left"); a.DECzp(PLAYER_X); a.label("no_left")
    # Right.
    a.LDAabs(0x4016); a.ANDi(0x01); a.BEQ("no_right"); a.INCzp(PLAYER_X); a.label("no_right")

    a.LDAi(0x02); a.STAabs(0x4014)
    a.PLA(); a.TAY(); a.PLA(); a.TAX(); a.PLA(); a.RTI()

    a.label("palettes")
    palettes = [
        0x0F, 0x01, 0x21, 0x31,
        0x0F, 0x06, 0x16, 0x26,
        0x0F, 0x09, 0x19, 0x29,
        0x0F, 0x0A, 0x1A, 0x2A,
        0x0F, 0x16, 0x27, 0x30,
        0x0F, 0x11, 0x21, 0x31,
        0x0F, 0x05, 0x15, 0x25,
        0x0F, 0x0C, 0x1C, 0x2C,
    ]
    a.emit(*palettes)
    a.patch()

    prg = bytearray([0xEA] * 0x4000)
    prg[:len(a.code)] = a.code
    nmi = a.labels["nmi"]
    reset = a.labels["reset"]
    prg[0x3FFA] = nmi & 0xFF; prg[0x3FFB] = (nmi >> 8) & 0xFF
    prg[0x3FFC] = reset & 0xFF; prg[0x3FFD] = (reset >> 8) & 0xFF
    prg[0x3FFE] = reset & 0xFF; prg[0x3FFF] = (reset >> 8) & 0xFF

    chr_rom = bytearray(0x2000)
    # Tile 1: a simple 8x8 smiley-ish block in color 1.
    tile = [0x3C, 0x7E, 0xDB, 0xFF, 0xA5, 0xDB, 0x7E, 0x3C]
    for row, bits in enumerate(tile):
        chr_rom[0x10 + row] = bits
        chr_rom[0x10 + 8 + row] = 0x00

    header = bytearray(b"NES\x1a")
    header.extend([1, 1, 0x00, 0x00])  # 16KB PRG, 8KB CHR, mapper 0, horizontal mirroring.
    header.extend([0] * 8)
    return bytes(header + prg + chr_rom)


# ---------------------------------------------------------------------------
# Tkinter GUI
# ---------------------------------------------------------------------------

class NESApp:
    def __init__(self, root: tk.Tk, initial_rom: Optional[str] = None, boot_demo: bool = False) -> None:
        self.root = root
        self.root.title("ChatGPT NES Emulator 0.1")
        self.scale = 2
        self.paused = False
        self.turbo = False
        self.nes: Optional[NES] = None
        self.photo = None
        self.raw_photo = None
        self.last_draw = 0.0
        self.frame_interval = 1.0 / 60.0

        self.canvas = tk.Canvas(root, width=PPU.WIDTH * self.scale, height=PPU.HEIGHT * self.scale,
                                highlightthickness=0, bg="black")
        self.canvas.pack(fill=tk.BOTH, expand=False)
        self.image_item = self.canvas.create_image(0, 0, anchor=tk.NW)
        self.status_var = tk.StringVar(value="No ROM loaded")
        self.status = tk.Label(root, textvariable=self.status_var, anchor="w")
        self.status.pack(fill=tk.X)

        self._build_menu()
        self._bind_keys()

        if initial_rom:
            self.load_file(initial_rom)
        elif boot_demo:
            self.load_demo()
        else:
            # Boot demo by default so the program starts with a playable scene.
            self.load_demo()

        self.root.after(1, self._main_loop)

    def _build_menu(self) -> None:
        menubar = tk.Menu(self.root)
        rom_menu = tk.Menu(menubar, tearoff=False)
        rom_menu.add_command(label="Open ROM...", command=self.open_rom_dialog)
        rom_menu.add_command(label="Boot built-in demo", command=self.load_demo)
        rom_menu.add_separator()
        rom_menu.add_command(label="Reset", command=self.reset)
        rom_menu.add_command(label="Pause / Resume", command=self.toggle_pause)
        rom_menu.add_separator()
        rom_menu.add_command(label="Exit", command=self.root.destroy)
        menubar.add_cascade(label="ROM", menu=rom_menu)

        view_menu = tk.Menu(menubar, tearoff=False)
        view_menu.add_command(label="1x", command=lambda: self.set_scale(1))
        view_menu.add_command(label="2x", command=lambda: self.set_scale(2))
        view_menu.add_command(label="3x", command=lambda: self.set_scale(3))
        menubar.add_cascade(label="View", menu=view_menu)

        help_menu = tk.Menu(menubar, tearoff=False)
        help_menu.add_command(label="Controls", command=self.show_controls)
        menubar.add_cascade(label="Help", menu=help_menu)
        self.root.config(menu=menubar)

    def _bind_keys(self) -> None:
        self.root.bind("<KeyPress>", self._on_key)
        self.root.bind("<KeyRelease>", self._on_key)
        self.root.focus_set()

    def _on_key(self, event: tk.Event) -> None:
        pressed = event.type == tk.EventType.KeyPress
        key = event.keysym
        mapping = {
            "z": "A", "Z": "A",
            "x": "B", "X": "B",
            "Return": "Start",
            "Shift_L": "Select", "Shift_R": "Select",
            "Up": "Up", "Down": "Down", "Left": "Left", "Right": "Right",
        }
        if key in mapping and self.nes:
            self.nes.bus.controllers[0].set_button(mapping[key], pressed)
        elif key in ("p", "P") and pressed:
            self.toggle_pause()
        elif key in ("r", "R") and pressed:
            self.reset()
        elif key == "Tab":
            self.turbo = pressed

    def set_scale(self, scale: int) -> None:
        self.scale = max(1, min(4, int(scale)))
        self.canvas.config(width=PPU.WIDTH * self.scale, height=PPU.HEIGHT * self.scale)
        self.draw_frame(force=True)

    def show_controls(self) -> None:
        messagebox.showinfo(
            "Controls",
            "A = Z\nB = X\nSelect = Shift\nStart = Enter\nD-pad = Arrow keys\n"
            "Pause = P\nReset = R\nTurbo = hold Tab\n\n"
            "Load .nes files through ROM > Open ROM. The built-in demo is legal homebrew data generated in memory.",
        )

    def open_rom_dialog(self) -> None:
        path = filedialog.askopenfilename(
            title="Open NES ROM",
            filetypes=[("NES ROMs", "*.nes"), ("All files", "*.*")],
        )
        if path:
            self.load_file(path)

    def load_file(self, path: str) -> None:
        try:
            self.nes = NES.from_file(path)
            self.paused = False
            self._update_status()
            if self.nes.cart.warning:
                messagebox.showwarning("Mapper warning", self.nes.cart.warning)
        except Exception as exc:
            messagebox.showerror("Could not load ROM", str(exc))

    def load_demo(self) -> None:
        try:
            self.nes = NES.from_bytes(make_builtin_demo_rom(), "Built-in Demo")
            self.paused = False
            self._update_status(extra="Use arrow keys to move the sprite")
        except Exception as exc:
            messagebox.showerror("Could not boot demo", str(exc))

    def reset(self) -> None:
        if self.nes:
            self.nes.reset()
            self.paused = False
            self._update_status(extra="Reset")

    def toggle_pause(self) -> None:
        self.paused = not self.paused
        self._update_status(extra="Paused" if self.paused else "Running")

    def _update_status(self, extra: str = "") -> None:
        if not self.nes:
            self.status_var.set("No ROM loaded")
            return
        cart = self.nes.cart
        msg = f"{cart.name} | {cart.mapper_name} | PRG {cart.prg_banks_16k}x16KB | CHR {cart.chr_banks_8k or 'RAM'}x8KB"
        if extra:
            msg += f" | {extra}"
        if cart.warning:
            msg += " | unsupported mapper fallback"
        self.status_var.set(msg)

    def _main_loop(self) -> None:
        now = time.perf_counter()
        if self.nes and not self.paused:
            should_run = self.turbo or (now - self.last_draw >= self.frame_interval)
            if should_run:
                frames = 3 if self.turbo else 1
                for _ in range(frames):
                    self.nes.run_until_next_frame()
                self.draw_frame()
                self.last_draw = now
        self.root.after(1, self._main_loop)

    def draw_frame(self, force: bool = False) -> None:
        if not self.nes:
            return
        rgb = bytes(self.nes.ppu.frame_rgb)
        header = f"P6\n{PPU.WIDTH} {PPU.HEIGHT}\n255\n".encode("ascii")
        # Tk PhotoImage accepts base64-encoded binary PPM data.
        data = base64.b64encode(header + rgb)
        try:
            self.raw_photo = tk.PhotoImage(data=data, format="PPM")
        except tk.TclError:
            # Fallback for Tk builds that expect text data.
            self.raw_photo = tk.PhotoImage(data=data.decode("ascii"), format="PPM")
        if self.scale != 1:
            self.photo = self.raw_photo.zoom(self.scale, self.scale)
        else:
            self.photo = self.raw_photo
        self.canvas.itemconfig(self.image_item, image=self.photo)


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Single-file Tkinter NES emulator")
    parser.add_argument("rom", nargs="?", help="Path to an iNES .nes ROM")
    parser.add_argument("--demo", action="store_true", help="Boot the built-in legal demo ROM")
    args = parser.parse_args(argv)

    root = tk.Tk()
    NESApp(root, initial_rom=args.rom, boot_demo=args.demo or not args.rom)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
