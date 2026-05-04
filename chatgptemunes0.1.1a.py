#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ac's nes emu 0.1 by chatgpt
Single-file educational NES emulator scaffold with:
- Tkinter GUI
- iNES ROM loading
- Mapper 0 / Mapper 2 PRG mapping
- 6502 CPU core subset + many official opcodes
- PPU framebuffer shell with NES palette viewer/background placeholder
- Controller input
- Procedural APU-style audio fallback using simpleaudio if available

This is NOT FCEUX-accurate yet. It is a clean starter core designed to grow.
Use only ROMs you legally own / homebrew ROMs.
"""

import math
import os
import sys
import time
import struct
import random
import threading
import queue
import tkinter as tk
from tkinter import filedialog, messagebox

TITLE = "ac's nes emu 0.1 by chatgpt"
SCREEN_W, SCREEN_H = 256, 240
MASTER_CLOCK = 1789773
FPS = 60
CPU_CYCLES_PER_FRAME = 29780

NES_PALETTE = [
    (84,84,84),(0,30,116),(8,16,144),(48,0,136),(68,0,100),(92,0,48),(84,4,0),(60,24,0),
    (32,42,0),(8,58,0),(0,64,0),(0,60,0),(0,50,60),(0,0,0),(0,0,0),(0,0,0),
    (152,150,152),(8,76,196),(48,50,236),(92,30,228),(136,20,176),(160,20,100),(152,34,32),(120,60,0),
    (84,90,0),(40,114,0),(8,124,0),(0,118,40),(0,102,120),(0,0,0),(0,0,0),(0,0,0),
    (236,238,236),(76,154,236),(120,124,236),(176,98,236),(228,84,236),(236,88,180),(236,106,100),(212,136,32),
    (160,170,0),(116,196,0),(76,208,32),(56,204,108),(56,180,204),(60,60,60),(0,0,0),(0,0,0),
    (236,238,236),(168,204,236),(188,188,236),(212,178,236),(236,174,236),(236,174,212),(236,180,176),(228,196,144),
    (204,210,120),(180,222,120),(168,226,144),(152,226,180),(160,214,228),(160,162,160),(0,0,0),(0,0,0)
]

class APU:
    def __init__(self, sample_rate=44100):
        self.sample_rate = sample_rate
        self.enabled = True
        self.running = False
        self.volume = 0.18
        self.pulse1_freq = 220.0
        self.pulse2_freq = 440.0
        self.tri_freq = 110.0
        self.noise = 0.02
        self.p1 = self.p2 = self.pt = 0.0
        self.q = queue.Queue(maxsize=4)
        try:
            import simpleaudio
            self.sa = simpleaudio
            self.available = True
        except Exception:
            self.sa = None
            self.available = False
            print("[APU] simpleaudio not installed; audio muted fallback")

    def write(self, addr, value):
        # Very rough register response, useful for hearing life from ROM writes.
        if addr in (0x4002, 0x4003):
            self.pulse1_freq = 80 + (value * 3)
        elif addr in (0x4006, 0x4007):
            self.pulse2_freq = 80 + (value * 2)
        elif addr in (0x400A, 0x400B):
            self.tri_freq = 55 + (value * 2)

    def start(self):
        if self.running:
            return
        self.running = True
        threading.Thread(target=self._thread, daemon=True).start()

    def stop(self):
        self.running = False

    def _chunk(self, seconds=0.05):
        n = int(self.sample_rate * seconds)
        out = bytearray()
        for _ in range(n):
            if not self.enabled:
                s = 0.0
            else:
                self.p1 = (self.p1 + self.pulse1_freq / self.sample_rate) % 1.0
                self.p2 = (self.p2 + self.pulse2_freq / self.sample_rate) % 1.0
                self.pt = (self.pt + self.tri_freq / self.sample_rate) % 1.0
                pulse1 = 1.0 if self.p1 < 0.5 else -1.0
                pulse2 = 1.0 if self.p2 < 0.25 else -1.0
                tri = 4.0 * abs(self.pt - 0.5) - 1.0
                nz = (random.random() * 2 - 1) * self.noise
                s = (pulse1 * 0.25 + pulse2 * 0.18 + tri * 0.25 + nz) * self.volume
            v = max(-32768, min(32767, int(s * 32767)))
            out += struct.pack("<h", v)
        return bytes(out)

    def _thread(self):
        while self.running:
            if self.available:
                data = self._chunk()
                self.sa.play_buffer(data, 1, 2, self.sample_rate)
            time.sleep(0.045)

class Cartridge:
    def __init__(self):
        self.prg = bytearray()
        self.chr = bytearray(8192)
        self.mapper = 0
        self.mirror = 0
        self.prg_banks = 0
        self.chr_banks = 0
        self.bank_select = 0

    def load(self, path):
        data = Path(path).read_bytes()
        if data[:4] != b"NES\x1a":
            raise ValueError("Not an iNES ROM")
        self.prg_banks = data[4]
        self.chr_banks = data[5]
        flags6, flags7 = data[6], data[7]
        self.mapper = (flags6 >> 4) | (flags7 & 0xF0)
        self.mirror = flags6 & 1
        trainer = 512 if (flags6 & 4) else 0
        off = 16 + trainer
        prg_size = self.prg_banks * 16384
        chr_size = self.chr_banks * 8192
        self.prg = bytearray(data[off:off + prg_size])
        off += prg_size
        self.chr = bytearray(data[off:off + chr_size]) if chr_size else bytearray(8192)
        if self.mapper not in (0, 2):
            raise ValueError(f"Mapper {self.mapper} not supported yet. Supported: 0/NROM, 2/UxROM")
        print(f"[ROM] PRG={self.prg_banks} CHR={self.chr_banks} mapper={self.mapper}")

    def cpu_read(self, addr):
        if addr < 0x8000:
            return 0
        if self.mapper == 0:
            if len(self.prg) == 16384:
                return self.prg[(addr - 0x8000) & 0x3FFF]
            return self.prg[(addr - 0x8000) & 0x7FFF]
        if self.mapper == 2:
            if addr < 0xC000:
                bank_count = max(1, len(self.prg) // 0x4000)
                base = (self.bank_select % bank_count) * 0x4000
                return self.prg[base + (addr - 0x8000)]
            base = len(self.prg) - 0x4000
            return self.prg[base + (addr - 0xC000)]
        return 0

    def cpu_write(self, addr, value):
        if self.mapper == 2 and addr >= 0x8000:
            self.bank_select = value & 0x0F

class Bus:
    def __init__(self, cart, apu):
        self.cart = cart
        self.apu = apu
        self.ram = bytearray(2048)
        self.ppu_regs = bytearray(8)
        self.controller = [0, 0]
        self.controller_shift = [0, 0]
        self.strobe = 0

    def read(self, addr):
        addr &= 0xFFFF
        if addr < 0x2000:
            return self.ram[addr & 0x7FF]
        if addr < 0x4000:
            return self.ppu_regs[addr & 7]
        if addr == 0x4016:
            v = self.controller_shift[0] & 1
            self.controller_shift[0] >>= 1
            return v | 0x40
        if addr >= 0x8000:
            return self.cart.cpu_read(addr)
        return 0

    def write(self, addr, value):
        addr &= 0xFFFF
        value &= 0xFF
        if addr < 0x2000:
            self.ram[addr & 0x7FF] = value
        elif addr < 0x4000:
            self.ppu_regs[addr & 7] = value
        elif 0x4000 <= addr <= 0x4015:
            self.apu.write(addr, value)
        elif addr == 0x4016:
            self.strobe = value & 1
            if self.strobe:
                self.controller_shift[0] = self.controller[0]
        elif addr >= 0x8000:
            self.cart.cpu_write(addr, value)

class CPU6502:
    C,Z,I,D,B,U,V,N = 1,2,4,8,16,32,64,128
    def __init__(self, bus):
        self.bus = bus
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.p = self.U | self.I
        self.pc = 0xC000
        self.cycles = 0
        self.stopped = False

    def reset(self):
        lo = self.bus.read(0xFFFC)
        hi = self.bus.read(0xFFFD)
        self.pc = (hi << 8) | lo
        if self.pc == 0:
            self.pc = 0xC000
        self.sp = 0xFD
        self.p = self.U | self.I
        self.stopped = False

    def f(self, flag, on=None):
        if on is None:
            return 1 if self.p & flag else 0
        if on: self.p |= flag
        else: self.p &= (~flag) & 0xFF

    def zn(self, v):
        v &= 0xFF
        self.f(self.Z, v == 0)
        self.f(self.N, v & 0x80)

    def rb(self):
        v = self.bus.read(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        return v

    def rw(self):
        lo = self.rb()
        hi = self.rb()
        return lo | (hi << 8)

    def push(self, v):
        self.bus.write(0x100 | self.sp, v)
        self.sp = (self.sp - 1) & 0xFF

    def pop(self):
        self.sp = (self.sp + 1) & 0xFF
        return self.bus.read(0x100 | self.sp)

    def imm(self): return self.rb()
    def zp(self): return self.rb()
    def zpx(self): return (self.rb() + self.x) & 0xFF
    def zpy(self): return (self.rb() + self.y) & 0xFF
    def abs(self): return self.rw()
    def abx(self): return (self.rw() + self.x) & 0xFFFF
    def aby(self): return (self.rw() + self.y) & 0xFFFF
    def izx(self):
        t = (self.rb() + self.x) & 0xFF
        return self.bus.read(t) | (self.bus.read((t + 1) & 0xFF) << 8)
    def izy(self):
        t = self.rb()
        return (self.bus.read(t) | (self.bus.read((t + 1) & 0xFF) << 8)) + self.y & 0xFFFF

    def adc(self, v):
        s = self.a + v + self.f(self.C)
        self.f(self.C, s > 0xFF)
        r = s & 0xFF
        self.f(self.V, (~(self.a ^ v) & (self.a ^ r) & 0x80) != 0)
        self.a = r
        self.zn(self.a)

    def sbc(self, v):
        self.adc((v ^ 0xFF) & 0xFF)

    def cmp(self, r, v):
        t = (r - v) & 0x1FF
        self.f(self.C, r >= v)
        self.zn(t & 0xFF)

    def branch(self, cond):
        off = self.rb()
        if off & 0x80: off -= 0x100
        if cond:
            self.pc = (self.pc + off) & 0xFFFF

    def step(self):
        if self.stopped:
            return 2
        op = self.rb()
        b = self.bus
        oldpc = self.pc - 1

        try:
            # Loads
            if op == 0xA9: self.a = self.imm(); self.zn(self.a)
            elif op == 0xA5: self.a = b.read(self.zp()); self.zn(self.a)
            elif op == 0xB5: self.a = b.read(self.zpx()); self.zn(self.a)
            elif op == 0xAD: self.a = b.read(self.abs()); self.zn(self.a)
            elif op == 0xBD: self.a = b.read(self.abx()); self.zn(self.a)
            elif op == 0xB9: self.a = b.read(self.aby()); self.zn(self.a)
            elif op == 0xA1: self.a = b.read(self.izx()); self.zn(self.a)
            elif op == 0xB1: self.a = b.read(self.izy()); self.zn(self.a)
            elif op == 0xA2: self.x = self.imm(); self.zn(self.x)
            elif op == 0xA6: self.x = b.read(self.zp()); self.zn(self.x)
            elif op == 0xB6: self.x = b.read(self.zpy()); self.zn(self.x)
            elif op == 0xAE: self.x = b.read(self.abs()); self.zn(self.x)
            elif op == 0xBE: self.x = b.read(self.aby()); self.zn(self.x)
            elif op == 0xA0: self.y = self.imm(); self.zn(self.y)
            elif op == 0xA4: self.y = b.read(self.zp()); self.zn(self.y)
            elif op == 0xB4: self.y = b.read(self.zpx()); self.zn(self.y)
            elif op == 0xAC: self.y = b.read(self.abs()); self.zn(self.y)
            elif op == 0xBC: self.y = b.read(self.abx()); self.zn(self.y)

            # Stores
            elif op == 0x85: b.write(self.zp(), self.a)
            elif op == 0x95: b.write(self.zpx(), self.a)
            elif op == 0x8D: b.write(self.abs(), self.a)
            elif op == 0x9D: b.write(self.abx(), self.a)
            elif op == 0x99: b.write(self.aby(), self.a)
            elif op == 0x81: b.write(self.izx(), self.a)
            elif op == 0x91: b.write(self.izy(), self.a)
            elif op == 0x86: b.write(self.zp(), self.x)
            elif op == 0x96: b.write(self.zpy(), self.x)
            elif op == 0x8E: b.write(self.abs(), self.x)
            elif op == 0x84: b.write(self.zp(), self.y)
            elif op == 0x94: b.write(self.zpx(), self.y)
            elif op == 0x8C: b.write(self.abs(), self.y)

            # Transfers
            elif op == 0xAA: self.x = self.a; self.zn(self.x)
            elif op == 0xA8: self.y = self.a; self.zn(self.y)
            elif op == 0x8A: self.a = self.x; self.zn(self.a)
            elif op == 0x98: self.a = self.y; self.zn(self.a)
            elif op == 0xBA: self.x = self.sp; self.zn(self.x)
            elif op == 0x9A: self.sp = self.x

            # Stack
            elif op == 0x48: self.push(self.a)
            elif op == 0x68: self.a = self.pop(); self.zn(self.a)
            elif op == 0x08: self.push(self.p | self.B | self.U)
            elif op == 0x28: self.p = self.pop() | self.U

            # Math
            elif op == 0x69: self.adc(self.imm())
            elif op == 0x65: self.adc(b.read(self.zp()))
            elif op == 0x75: self.adc(b.read(self.zpx()))
            elif op == 0x6D: self.adc(b.read(self.abs()))
            elif op == 0x7D: self.adc(b.read(self.abx()))
            elif op == 0x79: self.adc(b.read(self.aby()))
            elif op == 0x61: self.adc(b.read(self.izx()))
            elif op == 0x71: self.adc(b.read(self.izy()))
            elif op == 0xE9: self.sbc(self.imm())
            elif op == 0xE5: self.sbc(b.read(self.zp()))
            elif op == 0xF5: self.sbc(b.read(self.zpx()))
            elif op == 0xED: self.sbc(b.read(self.abs()))
            elif op == 0xFD: self.sbc(b.read(self.abx()))
            elif op == 0xF9: self.sbc(b.read(self.aby()))
            elif op == 0xE1: self.sbc(b.read(self.izx()))
            elif op == 0xF1: self.sbc(b.read(self.izy()))

            # Inc/Dec
            elif op == 0xE8: self.x = (self.x + 1) & 0xFF; self.zn(self.x)
            elif op == 0xC8: self.y = (self.y + 1) & 0xFF; self.zn(self.y)
            elif op == 0xCA: self.x = (self.x - 1) & 0xFF; self.zn(self.x)
            elif op == 0x88: self.y = (self.y - 1) & 0xFF; self.zn(self.y)
            elif op in (0xE6,0xF6,0xEE,0xFE):
                addr = {0xE6:self.zp,0xF6:self.zpx,0xEE:self.abs,0xFE:self.abx}[op]()
                v = (b.read(addr)+1)&255; b.write(addr,v); self.zn(v)
            elif op in (0xC6,0xD6,0xCE,0xDE):
                addr = {0xC6:self.zp,0xD6:self.zpx,0xCE:self.abs,0xDE:self.abx}[op]()
                v = (b.read(addr)-1)&255; b.write(addr,v); self.zn(v)

            # Logic
            elif op in (0x29,0x25,0x35,0x2D,0x3D,0x39,0x21,0x31):
                val = [self.imm, lambda:b.read(self.zp()), lambda:b.read(self.zpx()), lambda:b.read(self.abs()), lambda:b.read(self.abx()), lambda:b.read(self.aby()), lambda:b.read(self.izx()), lambda:b.read(self.izy())][(0x29,0x25,0x35,0x2D,0x3D,0x39,0x21,0x31).index(op)]()
                self.a &= val; self.zn(self.a)
            elif op in (0x09,0x05,0x15,0x0D,0x1D,0x19,0x01,0x11):
                val = [self.imm, lambda:b.read(self.zp()), lambda:b.read(self.zpx()), lambda:b.read(self.abs()), lambda:b.read(self.abx()), lambda:b.read(self.aby()), lambda:b.read(self.izx()), lambda:b.read(self.izy())][(0x09,0x05,0x15,0x0D,0x1D,0x19,0x01,0x11).index(op)]()
                self.a |= val; self.zn(self.a)
            elif op in (0x49,0x45,0x55,0x4D,0x5D,0x59,0x41,0x51):
                val = [self.imm, lambda:b.read(self.zp()), lambda:b.read(self.zpx()), lambda:b.read(self.abs()), lambda:b.read(self.abx()), lambda:b.read(self.aby()), lambda:b.read(self.izx()), lambda:b.read(self.izy())][(0x49,0x45,0x55,0x4D,0x5D,0x59,0x41,0x51).index(op)]()
                self.a ^= val; self.zn(self.a)

            # Compare
            elif op in (0xC9,0xC5,0xD5,0xCD,0xDD,0xD9,0xC1,0xD1):
                val = [self.imm, lambda:b.read(self.zp()), lambda:b.read(self.zpx()), lambda:b.read(self.abs()), lambda:b.read(self.abx()), lambda:b.read(self.aby()), lambda:b.read(self.izx()), lambda:b.read(self.izy())][(0xC9,0xC5,0xD5,0xCD,0xDD,0xD9,0xC1,0xD1).index(op)]()
                self.cmp(self.a, val)
            elif op in (0xE0,0xE4,0xEC):
                val = [self.imm, lambda:b.read(self.zp()), lambda:b.read(self.abs())][(0xE0,0xE4,0xEC).index(op)]()
                self.cmp(self.x, val)
            elif op in (0xC0,0xC4,0xCC):
                val = [self.imm, lambda:b.read(self.zp()), lambda:b.read(self.abs())][(0xC0,0xC4,0xCC).index(op)]()
                self.cmp(self.y, val)

            # Jumps / calls
            elif op == 0x4C: self.pc = self.abs()
            elif op == 0x6C:
                ptr = self.abs()
                lo = b.read(ptr)
                hi = b.read((ptr & 0xFF00) | ((ptr + 1) & 0xFF)) # 6502 bug
                self.pc = lo | (hi << 8)
            elif op == 0x20:
                target = self.abs()
                ret = (self.pc - 1) & 0xFFFF
                self.push((ret >> 8) & 255); self.push(ret & 255)
                self.pc = target
            elif op == 0x60:
                lo = self.pop(); hi = self.pop()
                self.pc = ((hi << 8) | lo) + 1 & 0xFFFF
            elif op == 0x40:
                self.p = self.pop() | self.U
                lo = self.pop(); hi = self.pop()
                self.pc = (hi << 8) | lo

            # Branches
            elif op == 0x90: self.branch(not self.f(self.C))
            elif op == 0xB0: self.branch(self.f(self.C))
            elif op == 0xF0: self.branch(self.f(self.Z))
            elif op == 0xD0: self.branch(not self.f(self.Z))
            elif op == 0x30: self.branch(self.f(self.N))
            elif op == 0x10: self.branch(not self.f(self.N))
            elif op == 0x50: self.branch(not self.f(self.V))
            elif op == 0x70: self.branch(self.f(self.V))

            # Flags
            elif op == 0x18: self.f(self.C, False)
            elif op == 0x38: self.f(self.C, True)
            elif op == 0x58: self.f(self.I, False)
            elif op == 0x78: self.f(self.I, True)
            elif op == 0xB8: self.f(self.V, False)
            elif op == 0xD8: self.f(self.D, False)
            elif op == 0xF8: self.f(self.D, True)

            # Shifts accumulator only + common memory
            elif op == 0x0A:
                self.f(self.C, self.a & 0x80); self.a=(self.a<<1)&255; self.zn(self.a)
            elif op == 0x4A:
                self.f(self.C, self.a & 1); self.a=(self.a>>1)&255; self.zn(self.a)
            elif op == 0x2A:
                c=self.f(self.C); self.f(self.C,self.a&0x80); self.a=((self.a<<1)&255)|c; self.zn(self.a)
            elif op == 0x6A:
                c=self.f(self.C); self.f(self.C,self.a&1); self.a=(self.a>>1)|(c<<7); self.zn(self.a)

            elif op == 0xEA:
                pass
            elif op == 0x00:
                self.stopped = True
                print(f"[CPU] BRK at ${oldpc:04X}")
            else:
                # Many unofficial opcodes become NOP for now.
                print(f"[CPU] Unimplemented opcode ${op:02X} at ${oldpc:04X} -> NOP")
        except Exception as e:
            print(f"[CPU] fault at ${oldpc:04X} op ${op:02X}: {e}")
            self.stopped = True

        self.cycles += 2
        return 2

class PPU:
    def __init__(self, cart):
        self.cart = cart
        self.frame = bytearray(SCREEN_W * SCREEN_H * 3)
        self.t = 0

    def render_placeholder(self, cpu):
        # Placeholder until cycle-accurate PPU is added.
        self.t += 1
        for y in range(SCREEN_H):
            for x in range(SCREEN_W):
                idx = ((x // 16) + (y // 16) + self.t // 10) & 63
                r,g,b = NES_PALETTE[idx]
                o = (y * SCREEN_W + x) * 3
                self.frame[o:o+3] = bytes((r,g,b))

        # CPU state overlay as colored bars
        vals = [cpu.a, cpu.x, cpu.y, cpu.pc & 255, cpu.sp, cpu.p]
        for i,v in enumerate(vals):
            color = NES_PALETTE[(v >> 2) & 63]
            for y in range(8 + i*10, 15 + i*10):
                for x in range(8, 8 + v):
                    if 0 <= x < SCREEN_W and 0 <= y < SCREEN_H:
                        o = (y * SCREEN_W + x) * 3
                        self.frame[o:o+3] = bytes(color)

class NESEmulator:
    def __init__(self):
        self.apu = APU()
        self.cart = Cartridge()
        self.bus = Bus(self.cart, self.apu)
        self.cpu = CPU6502(self.bus)
        self.ppu = PPU(self.cart)
        self.loaded = False
        self.paused = False

    def load_rom(self, path):
        self.cart.load(path)
        self.cpu.reset()
        self.loaded = True

    def reset(self):
        self.cpu.reset()

    def frame(self):
        if self.loaded and not self.paused:
            for _ in range(2000): # keep Tk responsive; not exact
                self.cpu.step()
                if self.cpu.stopped:
                    break
        self.ppu.render_placeholder(self.cpu)
        return self.ppu.frame

class App:
    def __init__(self, root):
        self.root = root
        root.title(TITLE)
        root.configure(bg="#151922")
        self.emu = NESEmulator()
        self.scale = 2

        top = tk.Frame(root, bg="#10151f")
        top.pack(fill="x")
        self.btn(top, "Load ROM", self.load_rom).pack(side="left", padx=4, pady=4)
        self.btn(top, "Reset", self.reset).pack(side="left", padx=4, pady=4)
        self.btn(top, "Pause", self.pause).pack(side="left", padx=4, pady=4)
        self.btn(top, "Mute", self.mute).pack(side="left", padx=4, pady=4)
        self.status = tk.Label(top, text="No ROM loaded", fg="#7dcfff", bg="#10151f", font=("Segoe UI", 10, "bold"))
        self.status.pack(side="left", padx=12)

        self.canvas = tk.Canvas(root, width=SCREEN_W*self.scale, height=SCREEN_H*self.scale,
                                bg="black", highlightthickness=2, highlightbackground="#2860ff")
        self.canvas.pack(padx=8, pady=8)
        self.img = tk.PhotoImage(width=SCREEN_W, height=SCREEN_H)
        self.canvas_img = self.canvas.create_image(0, 0, anchor="nw", image=self.img)
        self.canvas.scale(self.canvas_img, 0, 0, self.scale, self.scale)

        bottom = tk.Label(root, text="Controls: Z=A X=B Enter=Start Shift=Select Arrows=D-pad",
                          fg="#b8c7ff", bg="#151922")
        bottom.pack(pady=(0,6))

        root.bind("<KeyPress>", self.key_down)
        root.bind("<KeyRelease>", self.key_up)
        self.emu.apu.start()
        self.last = time.perf_counter()
        self.loop()

    def btn(self, parent, text, cmd):
        return tk.Button(parent, text=text, command=cmd, bg="black", fg="#00aaff",
                         activebackground="#111", activeforeground="#80d8ff",
                         font=("Segoe UI", 10, "bold"), relief="raised", bd=2)

    def load_rom(self):
        path = filedialog.askopenfilename(title="Open iNES ROM", filetypes=[("NES ROM", "*.nes"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.emu.load_rom(path)
            self.status.config(text=f"Loaded {os.path.basename(path)} | mapper {self.emu.cart.mapper}")
        except Exception as e:
            messagebox.showerror("ROM load error", str(e))

    def reset(self):
        self.emu.reset()
        self.status.config(text="Reset")

    def pause(self):
        self.emu.paused = not self.emu.paused
        self.status.config(text="Paused" if self.emu.paused else "Running")

    def mute(self):
        self.emu.apu.enabled = not self.emu.apu.enabled
        self.status.config(text="Muted" if not self.emu.apu.enabled else "Audio on")

    def key_mask(self, keysym):
        # NES: A B Select Start Up Down Left Right bits
        return {
            "z":1<<0, "Z":1<<0,
            "x":1<<1, "X":1<<1,
            "Shift_L":1<<2, "Shift_R":1<<2,
            "Return":1<<3,
            "Up":1<<4, "Down":1<<5, "Left":1<<6, "Right":1<<7,
        }.get(keysym, 0)

    def key_down(self, e):
        self.emu.bus.controller[0] |= self.key_mask(e.keysym)

    def key_up(self, e):
        self.emu.bus.controller[0] &= (~self.key_mask(e.keysym)) & 0xFF

    def draw(self, frame):
        # Tk PhotoImage fast-ish PPM update
        header = f"P6 {SCREEN_W} {SCREEN_H} 255 ".encode()
        self.img.tk.call(self.img, "put", header + bytes(frame), "-format", "PPM")
        if self.scale != 1:
            # PhotoImage scaling in canvas is limited; recreate zoomed image
            zoomed = self.img.zoom(self.scale, self.scale)
            self.canvas.itemconfig(self.canvas_img, image=zoomed)
            self.canvas.image_ref = zoomed

    def loop(self):
        frame = self.emu.frame()
        self.draw(frame)
        c = self.emu.cpu
        if self.emu.loaded and not self.emu.paused:
            self.status.config(text=f"A:{c.a:02X} X:{c.x:02X} Y:{c.y:02X} PC:{c.pc:04X} SP:{c.sp:02X}")
        self.root.after(int(1000/FPS), self.loop)

def main():
    root = tk.Tk()
    App(root)
    root.mainloop()

if __name__ == "__main__":
    main()
