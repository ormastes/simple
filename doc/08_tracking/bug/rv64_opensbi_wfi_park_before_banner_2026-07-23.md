# rv64 model: OpenSBI hangs in fw_platform_init (libfdt /cpus walk) before the banner

- **Filed:** 2026-07-23
- **Component:** `src/lib/hardware/rv64gc_rtl` core (instruction execution) — DTB
  tree-walk path; surfaces via OpenSBI `fw_jump` boot on `soc_top_64`
- **Severity:** Medium (model-only; the synthesizable RTL path to the FPGA is separate)
- **Status:** Open — root cause localized to the core's libfdt tree-walk execution

## Verified root cause (2026-07-23, after machine-ID CSR fix `7035b46`)

Booting `build/os/rv64_soc/fw_jump.bin` @0x8000_0000 + `soc_virt.dtb`
@0x8800_0000 (a1=0x8800_0000, a0=hartid=0), 256 MiB DRAM, on `soc_top_64` under
the interpreter:

- Runs **trap-free** (`mcause=0`) — the machine-ID CSR illegal-trap is gone.
- Parks in an unconditional `wfi;wfi;j .` loop at **pc=0x8000_4A40**, M-mode.
  Symbols (`fw_jump.elf`) resolve this to **`fw_platform_init`**'s
  `fail: while (1) wfi();` at `platform/generic/platform.c:141`.
- It reaches the hang via `bltz a0,fail` after
  **`fdt_path_offset(fdt, "/cpus")`** (platform.c:115) returns
  **`a0 = -4 = -FDT_ERR_BADOFFSET`**. The earlier `fdt_path_offset(fdt, "/")`
  (platform.c:99) SUCCEEDED, so the FDT header and pointer are valid and the
  first level of struct-block parsing works.
- `uart_tx` length = 0 (hang is before console init, so no message is printed).

**Memory is NOT the problem — proven.** Reading the DTB back through the model's
memory path (`ram64_read`, the same LSU path the core uses) returns the exact
file bytes: `d0 0d fe ed 00 00 06 1b 00 00 00 38 00 00 04 d4 ...`,
`totalsize=0x0000_061b=1563` matching the on-disk `soc_virt.dtb`. The DTB is
byte-for-byte intact at 0x8800_0000.

**Conclusion:** the core **mis-executes libfdt's DTB tree-walk** when descending
from root to the `/cpus` subnode. `fdt_offset_ptr` returns `-FDT_ERR_BADOFFSET`,
meaning the walk computed an out-of-bounds struct-block offset. Not a memory,
CSR, DTB, or trap issue.

**Byte loads are proven correct** — the DTB readback above used
`ram64_read(width=1)` (the same width-1 path the LSU takes for `lbu`) and
returned exact per-byte values. So the suspicion narrows from "byte loads" to the
**offset arithmetic / token-skip control flow** of the walk: the big-endian u32
assembly (`fdt32_ld` shift/or), the property-length skip
(`FDT_TAGALIGN(len)` rounding), or a signed/unsigned compare in the token loop —
one of these computes a wrong advance so the next `fdt_offset_ptr` bounds-check
trips. (A bare-core `lbu`-at-offset probe was attempted but is unreliable: it
bypasses `ram64`, so its result is a harness artifact, not evidence.)

## Next step to isolate the exact instruction

Difftest the boot against a reference (spike / QEMU TCG) and compare the
pc/register stream through `fdt_path_offset`; the first divergence is the
mis-executed instruction. `fw_platform_init` runs within the first ~50k ticks
from reset (~90 s under the interpreter at ~580 ticks/s), so the walk is a
bounded, few-thousand-instruction window — practical to trace once anchored.
Candidate op classes to scrutinize first: `lbu` zero-extension, the shift/or
big-endian assembly, and any unaligned halfword/word load in the token skip.

## Blocker on iterating

The interpreter runs the full `soc_top_64` model at **~580 ticks/s** (50k / 86 s);
the seed JIT miscompiles the model (see the FPU/UART interpreter-only probes), so
JIT can't speed it up. This makes instruction-level boot tracing slow but not
impossible for this bounded window. A Linux boot (billions of ticks) remains
impractical via the per-cycle interpreter — the synthesizable RTL + hardware/QEMU
harness is the route for full-OS bring-up.

## Repro

`SIMPLE_EXECUTION_MODE=interpreter src/compiler_rust/target/bootstrap/simple run`
a driver that loads fw_jump.bin@0 + soc_virt.dtb@0x8000000 into a 256 MiB
`soc_top_64`, sets pc=0x80000000 / a0=0 / a1=0x88000000, chunk-runs
`soc_top_64_run`, and dumps trap state + pc when max_pc stalls. Symbol resolution:
`riscv64-unknown-elf-addr2line -f -e
build/os/rv64_soc/opensbi-src/build/platform/generic/firmware/fw_jump.elf <pc>`.
