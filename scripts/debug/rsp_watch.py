#!/usr/bin/env python3
# rsp_watch.py -- scripted RSP (gdb remote serial protocol) client for
# in-guest write-watchpoint debugging of the riscv64 SimpleOS kernels.
#
# Why this exists: the project host has no riscv64-capable gdb, and the
# freestanding guests have no MMU for guard-page write protection. QEMU's
# gdbstub DOES accept Z2/Z3 (hardware watchpoint) packets on riscv64, so a
# small scripted client gets data watchpoints the toolchain cannot otherwise
# provide. Proven on the par_state-overlay hunt
# (doc/08_tracking/bug/riscv64_in_guest_parse_recursion_par_state_uninit_2026-11-05.md,
# 2026-11-06 section): caught the overlaying zero-fill live at pc precision.
#
# Harness (kernel per scripts/os/build-simpleos-riscv64-interpreter-kernel.shs,
# OpenSBI v1.4 fw_payload wrap per the check gate):
#   qemu-system-riscv64 ... -S -gdb tcp:127.0.0.1:<port> -bios <fw_payload.bin>
#   python3 scripts/debug/rsp_watch.py <kernel.elf> <port>
#
# Flow: break at the parser module's dynamic-init entry (anchor), continue to
# its caller's continuation (the init has then stored par_state), read the
# global to derive the block range, then arm a Z2 write watchpoint on the
# block plus decrease-filters on all three runtime bump cursors (g_heap_off).
#
# Hard-won notes:
#   * The stub returns registers as raw little-endian bytes hex-encoded:
#     int.from_bytes(bytes.fromhex(reply), "little"), NOT int(reply, 16).
#   * QEMU stops BEFORE the watched instruction commits: memory reads at a
#     watchpoint stop show the PRE-write value.
#   * One stub connection at a time; a second client interleaves packets and
#     both crawl. Kill the VM between sessions -- Z2 watchpoints persist.
#   * Watchpoint hits during crt0.S .bss zeroing are expected noise; anchor
#     after _start_kernel (the parser-init anchor here) or filter zero writes.

import bisect
import re
import socket
import struct
import subprocess
import sys
import time

NM = "/usr/lib/llvm-18/bin/llvm-nm"


def symbols(elf):
    out = subprocess.run([NM, elf], capture_output=True, text=True).stdout
    return {p[-1]: int(p[0], 16) for p in (l.split() for l in out.splitlines()) if len(p) >= 3}


class Rsp:
    def __init__(self, port):
        self.s = socket.create_connection(("127.0.0.1", port), timeout=60)
        self.s.settimeout(300)

    def _recv(self):
        while True:
            c = self.s.recv(1)
            if not c:
                raise ConnectionError("stub closed")
            if c != b"+":
                return c

    def get_packet(self):
        while self._recv() != b"$":
            pass
        body = b""
        while True:
            c = self._recv()
            if c == b"#":
                break
            body += c
        self.s.recv(2)
        self.s.sendall(b"+")
        return body.decode()

    def cmd(self, body):
        pkt = b"$" + body.encode() + b"#" + b"%02x" % (sum(body.encode()) % 256)
        for _ in range(5):
            self.s.sendall(pkt)
            while True:
                c = self.s.recv(1)
                if c == b"+":
                    return self.get_packet()
                if c == b"-":
                    break
        raise RuntimeError("NAK storm")

    def cont(self):
        self.s.sendall(b"$c#63")
        return self.get_packet()

    def z0(self, addr):
        return self.cmd(f"Z0,{addr:x},4") == "OK"

    def z2(self, addr, length):
        return self.cmd(f"Z2,{addr:x},{length:x}")

    def read_mem(self, addr, length):
        return bytes.fromhex(self.cmd(f"m{addr:x},{length:x}"))

    def reg(self, n):
        return int.from_bytes(bytes.fromhex(self.cmd(f"p{n:x}")), "little")

    def pc(self):
        return self.reg(32)

    def ra(self):
        return self.reg(1)


def main():
    elf, port = sys.argv[1], int(sys.argv[2])
    sym = symbols(elf)
    par_state = sym["compiler__frontend__core__parser__par_state"]
    parser_dyn = sym["__module_init_compiler__frontend__core__parser_dynamic"]
    print(f"[rsp] par_state={par_state:#x} parser_dyn={parser_dyn:#x}", flush=True)

    rsp = Rsp(port)
    rsp.cmd("qSupported:multiprocess+")
    rsp.cmd("Hg0")

    # Phase 1: anchor after the parser module's init has stored par_state.
    assert rsp.z0(parser_dyn), "Z0 parser_dyn failed"
    stop = rsp.cont()
    assert rsp.pc() == parser_dyn, f"anchor pc {rsp.pc():#x}"
    ret_addr = rsp.ra()
    rsp.cmd(f"z0,{parser_dyn:x},4")
    assert rsp.z0(ret_addr)
    rsp.cont()
    assert rsp.pc() == ret_addr, f"return-cont pc {rsp.pc():#x}"
    rsp.cmd(f"z0,{ret_addr:x},4")

    val = struct.unpack("<Q", rsp.read_mem(par_state, 8))[0]
    lo, hi = val & ~7, (val & ~7) + 0x80
    print(f"[rsp] par_state={val:#x} block=[{lo:#x},{hi:#x})", flush=True)

    # Phase 2: arm block write watch + cursor decrease filters, run.
    nmout = subprocess.run([NM, elf], capture_output=True, text=True).stdout
    curs = [int(l.split()[0], 16) for l in nmout.splitlines() if l.split() and l.split()[-1] == "g_heap_off"]
    print(f"[rsp] arming block + cursors {[hex(c) for c in curs]}", flush=True)
    assert rsp.z2(lo, 0x80) == "OK", "block Z2 rejected"
    for c in curs:
        rsp.z2(c, 8)

    sym_list = sorted(symbols(elf).items(), key=lambda kv: kv[1])

    def near(a):
        i = bisect.bisect_right([v for _, v in sym_list], a) - 1
        return sym_list[i][0] if i >= 0 else hex(a)

    cur_prev = {c: None for c in curs}
    for i in range(100000):
        stop = rsp.cont()
        w = re.search(r"watch:([0-9a-f]+)", stop)
        pc = rsp.pc()
        if w and any(hex(c)[2:] == w.group(1) for c in curs):
            for c in curs:
                v = struct.unpack("<Q", rsp.read_mem(c, 8))[0]
                pv = cur_prev[c]
                if pv is not None and v < pv:
                    print(f"[rsp] !!! CURSOR {c:#x} DECREASE {pv:#x}->{v:#x} at pc={pc:#x} ({near(pc)}) ra={rsp.ra():#x} ({near(rsp.ra())})", flush=True)
                    return
                cur_prev[c] = v
        else:
            print(f"[rsp] BLOCK WRITE at pc={pc:#x} ({near(pc)}) ra={rsp.ra():#x} ({near(rsp.ra())}) stop={stop}", flush=True)
            return
        if i % 2000 == 0:
            print(f"[rsp] ...{i}", flush=True)
    print("[rsp] no event", flush=True)


if __name__ == "__main__":
    main()
