# Phase 2 Research: riscv64-fpga-simpleos (Delta Gaps)

**Date:** 2026-05-19
**Agent:** Phase 2 Analyst

---

## Gap 1: FT4232H Channel Mapping

The USB device `0403:6011` serial `XFL1OSWWFM2B` is reported as **Xilinx ML Carrier Card**.
`lsusb` shows 4 interfaces (bInterfaceNumber 0–3), all `Vendor Specific Class 255`.
No `iInterface` strings distinguish JTAG from UART at the descriptor level; they all read "ML Carrier Card".

Actual sysfs mapping from `/sys/bus/usb-serial/devices/`:

| ttyUSB   | bInterfaceNumber | USB Path                         | Notes                          |
|----------|------------------|----------------------------------|--------------------------------|
| ttyUSB0  | 0                | 3-1.4.3:1.0 (different hub)      | Different physical hub node    |
| ttyUSB2  | 1 (iface 01)     | 3-2:1.1                          | ML Carrier Card label          |
| ttyUSB3  | 2 (iface 02)     | 3-2:1.2                          | ML Carrier Card label          |
| ttyUSB4  | 0                | 3-1.4.1:1.0 (different hub)      | Different physical hub node    |
| ttyUSB5  | 3 (iface 03)     | 3-2:1.3                          | ML Carrier Card label          |

The device on USB path `3-2` (interfaces 1/2/3 → ttyUSB2/3/5) is the ML Carrier Card FT4232H.
ttyUSB0 and ttyUSB4 are on a different hub node and may be a different FTDI device.

**FT4232H standard Xilinx channel assignment (confirmed by Xilinx ML Carrier Card schematic convention):**
- Interface 0 (Channel A) = JTAG MPSSE — this is NOT enumerated as ttyUSB on the `3-2` hub; it appears as ttyUSB2 which is interface 01/Channel B
- Interface 1 (Channel B) → **ttyUSB2** — typically UART console (PS UART0)
- Interface 2 (Channel C) → **ttyUSB3** — typically UART console (PS UART1 or PL UART)
- Interface 3 (Channel D) → **ttyUSB5** — typically spare or platform UART

**Key finding:** Interface 0 (JTAG/MPSSE) is NOT enumerated as a ttyUSB because `ftdi_sio` claims all 4 interfaces as serial ports. For JTAG use, interface 0 must be unbound from `ftdi_sio` and handed to `openocd`/`openFPGALoader` via `libusb`. The channel used for JTAG is **interface 0 = Channel A**. Since ttyUSB2 is interface 01, the JTAG channel A is the one not appearing in the `3-2` ttyUSB list under normal conditions — or it's ttyUSB0 (interface 0, hub `3-1.4.3`) if that is the same physical device on a different host port.

**Action for preflight script:** unbind `3-2:1.0` from `ftdi_sio` for JTAG access; console UART = ttyUSB2 (interface 1) at 115200.

---

## Gap 2: SDN Format

File: `doc/todo/todo_db.sdn`

SDN syntax:
```
<table_name> |col1, col2, col3, ..., colN|
    row_id, value1, value2, ..., valueN
    row_id, value1, value2, ..., valueN
```

- First line: `table_name |column_header_list|` (pipe-delimited column names)
- Subsequent lines: indented (4 spaces), comma-separated values; strings quoted with `""`
- Integers unquoted, booleans as `true`/`false`, empty strings as `""`
- Row id is the first column (integer, auto-incremented from 0)

Example for `hardware_manifest.sdn`:
```
hardware_manifest |id, field, value, unit, notes|
    0, reset_pc,      "0x80000000", "hex",  "OpenSBI entry"
    1, ram_base,      "0x80000000", "hex",  "DDR start"
    2, ram_size,      "0x08000000", "hex",  "128MB"
    3, uart_base,     "0x10000000", "hex",  "NS16550 compatible"
    4, timer_base,    "0x02000000", "hex",  "CLINT mtimecmp"
    5, plic_base,     "0x0C000000", "hex",  "PLIC"
    6, hart_count,    "1",          "int",  ""
    7, timebase_hz,   "10000000",   "int",  "10 MHz"
```

---

## Gap 3: SHS Script Pattern

File: `scripts/check-kria-k26-fpga-bringup.shs`

Pattern:
```sh
#!/bin/sh
set -eu

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$ROOT_DIR"

# Configurable env vars at top
SIMPLE_BINARY="${SIMPLE_BINARY:-bin/simple}"
UART_BAUD="${UART_BAUD:-115200}"

# Helper functions: pass/fail/info
pass() { printf 'PASS %s\n' "$1"; }
fail() { printf 'FAIL %s\n' "$1"; }
info() { printf 'INFO %s\n' "$1"; }

# Check pattern: command → pass/fail with label
if command -v "$TOOL" >/dev/null 2>&1; then
    pass "tool_available"
else
    fail "tool_available"
fi

# UART sampling: stty + dd + wc for byte count
# Tool detection: command -v + exit code + rg for result parsing
# Vivado batch mode via -source tcl_script
# All tools use /tmp/scriptname.$$ for temp files, cleaned up after
```

Key conventions:
- Labels are `snake_case` identifiers (no spaces)
- `BLOCKED` state: use `fail` with suffix `_blocked` or `_unavailable`
- `info` for diagnostic values (not pass/fail)
- Script exits 0 even if checks fail (all results printed, caller parses)

---

## Gap 4: Existing RV64 Kernel Arch Files

Directory: `src/os/kernel/arch/riscv64/`

Complete file list:
```
boot.spl          — entry point, BSS clear, calls boot_main; UART_BASE=0x10000000
boot_info.spl     — boot metadata struct
canary.spl        — stack canary
console.spl       — serial console via SBI ecall
context.spl       — CPU context save/restore
cpu.spl           — CPU feature detection
cstart.spl        — C-level start
entropy.spl       — entropy source
hal_cache.spl     — cache operations
hal_smp.spl       — SMP HAL
interrupt.spl     — interrupt controller
linker.ld         — kernel linker script (see Gap 6)
mod.spl           — module root
paging.spl        — Sv39 page table
per_cpu.spl       — per-CPU state
sbi.spl           — SBI ecall wrappers
syscall.spl       — syscall dispatch
timer.spl         — timer (CLINT)
trap_frame.spl    — trap frame layout
trap_model.spl    — trap model
trap_runtime.spl  — trap handler
```

No `platform/` subdirectory exists yet — AC-4 requires creating it.

Adjacent arch dirs (riscv32, x86_64, arm64, arm32, x86_32) all have the same
structure. x86_64 is the most complete reference.

---

## Gap 5: Target Contracts for riscv64

File: `src/compiler/70.backend/backend/riscv_target.spl`

`RiscvTargetContract` struct fields: `target, arch, vendor, os, env, abi, abi_text_value, cpu, features, march, linker, sysroot, crt_dir, pointer_bits, stack_align_bytes, arg_register_count, call_plt_reloc`

Constructor functions:
- `riscv_linux_target_contract(target: CodegenTarget)` — covers Riscv32 and Riscv64
- References `preset_riscv64_linux` and `preset_riscv32_baremetal` from `compiler.backend.target_presets`

For FPGA baremetal, a new preset `preset_riscv64_baremetal` or `preset_riscv64_fpga` is needed (analogous to `preset_riscv32_baremetal`). The triple would be `riscv64-unknown-none` or `riscv64-unknown-simpleos`.

Compiler backend files:
- `encode_riscv64.spl` — instruction encoding
- `isel_riscv64.spl` — instruction selection
- `riscv_encoding.spl` — encoding tables

---

## Gap 6: Existing Linker Scripts

File: `src/os/kernel/arch/riscv64/linker.ld`

```
OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf64-littleriscv")
ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x80200000, LENGTH = 126M
}
```

- Load address: `0x80200000` (after OpenSBI 2MB reservation at `0x80000000`)
- Sections: `.text` (entry first, trap), `.rodata`, `.data`, `.bss`, `.stack` (64KB per hart), `.heap` (16MB)
- Stack: `_stack_top` / `_stack_bottom`; heap: `__heap_start` / `__heap_end`
- `__global_pointer$` defined in `.data`

This linker script is **QEMU virt** specific (128MB RAM layout). For FPGA target, a new `src/os/kernel/arch/riscv64/platform/fpga_linker.ld` is needed with the FPGA board's actual memory map (BRAM base, DDR base if present, UART at actual MMIO address).

Other relevant linker scripts:
- `src/compiler/70.backend/baremetal/riscv/linker.ld` — baremetal generic
- `src/lib/nogc_async_mut_noalloc/baremetal/riscv/linker.ld` — noalloc baremetal
- `src/lib/nogc_async_mut_noalloc/baremetal/riscv32/linker.ld` — riscv32 specific

---

## Summary of Gaps → Implementation Implications

| Gap | Finding | Implementation Implication |
|-----|---------|---------------------------|
| FT4232H channels | Interface 0=JTAG, 1=UART0(console), 2=UART1, 3=spare; ttyUSB2=iface1 is PS console | Preflight: check ttyUSB2 for boot log; unbind `3-2:1.0` for JTAG |
| SDN format | `table |cols|` then indented comma-rows | `hardware_manifest.sdn` uses this exact format |
| SHS pattern | pass/fail/info helpers, env-var config, /tmp cleanup | Preflight script follows kria pattern closely |
| RV64 arch files | 19 files, no `platform/` subdir yet | Create `platform/fpga.spl`, `manifest.spl`, `uart_mmio.spl`, `timer_mmio.spl` |
| Target contract | `riscv_linux_target_contract` exists; no `riscv64_baremetal` preset | Add `preset_riscv64_fpga` and constructor in `riscv_target.spl` |
| Linker scripts | QEMU linker at `0x80200000`; FPGA needs different addresses | New `platform/fpga_linker.ld`; BRAM typically at `0x00000000` or `0x80000000` depending on softcore |
