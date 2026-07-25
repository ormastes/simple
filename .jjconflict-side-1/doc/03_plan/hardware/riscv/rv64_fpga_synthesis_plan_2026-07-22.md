# RV64 FPGA Synthesis Plan (2026-07-22)

Author: Lane GG (Wave 5). Scope: reverse the RV32 VHDL flow, attempt the same
for RV64, produce a deterministic generator + honest per-module status +
ordered unblock lanes. No Vivado full run performed (synth-only was permitted
if free; not exercised — see §6).

## 1. Executive summary

**RV32 has a real bitstream on K26 (8ef2719412e, DONE=HIGH, WNS +16.932ns,
13.3% LUT / 26% BRAM). RV64 does not, and cannot today: the generator hard
-crashes on a phantom API before it ever reaches the CPU core.** Beyond that
crash, direct probing of the real `.spl` RTL modules shows the "compile `.spl`
RTL straight to VHDL" route was never functional for either architecture —
both rv32 and rv64 bitstreams that exist (rv32) or would exist (rv64) come
from **hand-authored VHDL generators**, not from lowering `rv32i_rtl` /
`rv64gc_rtl` source through the compiler's VHDL backend. This is the single
most important fact this lane found: the "template route" is not a stand-in
for a working compile path that will be swapped in later — it IS the
production path, for both architectures, and always has been.

## 2. How RV32 really produces synthesizable VHDL (reverse-engineered)

`scripts/fpga/generate_rv32_vhdl.shs` calls `scripts/fpga/rv32_vhdl_driver.spl`,
which does three genuinely different things, none of which is "compile
`rv32i_rtl/*.spl` to VHDL":

1. **`render_rv32i_opcode_package()` / `render_rv32i_field_extractor()` /
   `render_rv32i_alu_control()`** (defined in the compiler's
   `compiler.backend.vhdl` support code, e.g.
   `src/compiler/70.backend/backend/vhdl/vhdl_rv32i_decode.spl`,
   `vhdl_register_file.spl`) — these are Simple **functions that build VHDL
   text programmatically**. They produce `rv32i_pkg.vhd`, `rv32i_decode.vhd`,
   `rv32i_regfile.vhd`. Real, working, checked (`grep -q 'entity
   rv32i_regfile is'`). They do **not** read `rv32i_rtl/*.spl` at all.
2. **`RiscvFpgaLane.rv32_default().hardware_source_spl()`** — writes a
   *synthetic* `rv32_core.spl` containing hand-typed `@hardware fn
   simple_rv32i_core_decode_writeback(...)` etc. (defined inline in
   `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl:739+`, NOT sourced from
   `rv32i_rtl/`). The driver *does* attempt
   `bin/simple compile --backend=vhdl rv32_core.spl -o rv32_core.vhd` on this
   — the one genuine "compile RTL-annotated `.spl` to VHDL" attempt in the
   whole flow — and it fails (filed: seed compiler VHDL-backend limitation).
   The generator script degrades this to a non-fatal warning because synthesis
   never consumes `rv32_core.vhd` anyway.
3. **Hand-written VHDL templates**, copied verbatim from
   `examples/09_embedded/fpga_riscv/rtl/{rv32_exec_core,soc_top_rv32,
   soc_top_rv32_sim}.vhd` into `build/vhdl/rv32/`. **This is the actual CPU
   core and SoC top that got routed and DONE=HIGH on the K26.** It is
   maintained by hand in `examples/`, versioned in git like any other source
   file, and kept "in sync" only by developer discipline (there is no
   generator, round-trip test, or automated check that `rv32i_rtl/*.spl` and
   this template agree on ISA behavior beyond the difftest/riscv-tests lanes
   that exercise the interpreter, not the VHDL).

So the honest description of "the rv32 template route": it is hand-written
VHDL, authored directly for FPGA synthesis, never derived from
`rv32i_rtl/*.spl`, and stays "in sync" with the Simple-side model only via
separate proof lanes (difftest, ISA conformance probes) that check behavioral
equivalence, not code provenance.

## 3. RV64: what exists, what breaks (with exact error text)

### 3.1 The generator crashes before the CPU core

`scripts/fpga/rv64_vhdl_driver.spl` imports:

```
use std.hardware.fpga_linux.riscv_fpga_linux.{compile_to_vhdl_module}
```

`compile_to_vhdl_module` **is never defined anywhere in `src/`**
(`grep -rn "fn compile_to_vhdl_module" src/` — zero hits, confirmed twice this
session). Running the driver reproduces this every time, with two distinct
observed failure surfaces on the identical missing-symbol condition:

```
error[E1002]: function `compile_to_vhdl_module` not found
  = help: check the function name or import the module that defines it
```
— OR, non-deterministically on the same input —
```
Segmentation fault (core dumped)
```//(`bin/simple run scripts/fpga/rv64_vhdl_driver.spl`, exit 139)

Both were reproduced multiple times in this session on an unmodified worktree
(base `f4a2165f389`). The nondeterminism (clean E1002 vs. raw SIGSEGV for the
*same* missing-function resolution) is itself worth flagging as a seed-runtime
robustness gap — a symbol-resolution failure should never have a code path
that segfaults instead of erroring — but is out of this lane's file set
(interpreter, not `scripts/fpga/` or the plan doc).

Because of this crash, only the first two of nineteen expected `.vhd` files
ever get written: `soc_top_rv64.vhd` and `soc_top_rv64_k26.vhd` (both from
hand-authored string-building functions in the driver itself —
`generate_soc_top_vhdl_rv64()` / `gen_k26_top()`, the rv64 analogs of step 1
above). Everything downstream — `rv64gc_core`, and all six peripheral stubs
(`clint`, `plic`, `uart`, `ram`, `bootrom`, `wb_interconnect`) that
`soc_top_rv64.vhd` directly instantiates — never gets generated.

### 3.2 What GHDL says about the two files that DO exist

```
ghdl -a --std=08 build/vhdl/rv64/soc_top_rv64.vhd
  error: unit "rv64gc_core" not found in library "work"
  error: unit "clint" not found in library "work"
  error: unit "plic" not found in library "work"
  error: unit "uart" not found in library "work"
  error: unit "ram" not found in library "work"
  error: unit "bootrom" not found in library "work"
  error: unit "wb_interconnect" not found in library "work"

ghdl -a --std=08 build/vhdl/rv64/soc_top_rv64_k26.vhd
  error: cannot find resource library "unisim"
  error: unit "vcomponents" not found in library "unisim"
```

`soc_top_rv64.vhd` uses VHDL-2008 **direct entity instantiation**
(`entity work.rv64gc_core`), which GHDL resolves at **analysis** time (not
just elaboration), so it cannot analyze standalone until the 7 missing units
exist in the same library. `soc_top_rv64_k26.vhd`'s failure (missing `unisim`)
is expected and separate — it is the Xilinx-primitives K26 top, analogous to
rv32's `soc_top_rv32.vhd` (which also needs `unisim`/`STARTUPE3`/`BUFGCE_DIV`
and is never GHDL-analyzed standalone either; only `soc_top_rv32_sim.vhd`,
the sim-only top, is GHDL-clean). **`soc_top_rv64.vhd` is architecturally the
rv64 analog of `soc_top_rv32_sim.vhd`** (no unisim references) — it would
likely analyze cleanly too, once the 7 missing units exist.

### 3.3 Bypassing the phantom function: does `rv64gc_rtl/*.spl` compile directly?

To answer requirement 2 honestly, this lane invoked
`bin/simple compile --backend=vhdl` **directly** on each real RTL module in
`src/lib/hardware/rv64gc_rtl/` (mirroring rv32's one genuine compile attempt),
bypassing the missing driver function entirely:

| Module | Result |
|---|---|
| pkg, alu, regfile, csr_s, csr, decode, lsu, mmu_sv39, mul_div, atomics | `error: VHDL compilation failed: codegen: VHDL backend found no hardware functions to emit` |
| core | `error: VHDL compilation failed: semantic: Undefined("undefined identifier: OP_MISC_MEM")` |

Two distinct, real root causes, confirmed by source inspection:

- **"no hardware functions to emit"**: `grep -c "@hardware" src/lib/hardware/rv64gc_rtl/*.spl` is **0 for every file** — none of the RTL modules carry the `@hardware` annotation the VHDL backend requires to lower a function. This is **not rv64-specific**: `grep -c "@hardware" src/lib/hardware/rv32i_rtl/*.spl` is also **0 for every file**. Neither architecture's plain RTL-model source was ever written to be VHDL-backend-compilable; rv32's one working compile target (`rv32_core.spl`) is a hand-typed synthetic file with real `@hardware fn`s, generated on the fly and never derived from `rv32i_rtl/`.
- **`OP_MISC_MEM` undefined**: this one IS a genuine, fixable rv64-side source bug, independent of the `@hardware` gap. `src/lib/hardware/rv64gc_rtl/core.spl:20` imports `OP_MISC_MEM` from its sibling `std.hardware.rv64gc_rtl.pkg`, but `rv64gc_rtl/pkg.spl`'s export list (lines 185-204) never defines or re-exports `OP_MISC_MEM` — it exports `OP_BRANCH, OP_LOAD, OP_STORE, OP_SYSTEM` etc. but not the FENCE opcode. The constant does exist elsewhere (`src/lib/hardware/riscv_common/decode.spl:29`, `val OP_MISC_MEM: i64 = 0x0F`) and is even re-exported by `riscv_common/__init__.spl:25` — just not through the import path `core.spl` actually uses.

## 4. Template-route honest evaluation, applied to RV64

Given §2-§3, an rv64 hand-written template is not a stopgap around a "nearly
working" compiler path — it is the **only** route either architecture has
ever used to reach silicon. Building one is the correct near-term plan, not a
compromise. Estimated authoring cost, using the rv32 template
(`rv32_exec_core.vhd`, 1656 lines including comments) as the size baseline:

- Register file: 32×64-bit vs. 32×32-bit — mechanical width change, ~1 day.
- ALU: RV64I adds `*W` (32-bit-result-in-64-bit-reg) variants (`ADDW/SUBW/
  SLLW/SRLW/SRAW`) atop the RV32 ops — ~2-3 days including the sign-extend
  edge cases.
- Decode: wider immediates, `*W` opcodes, RV64-specific `SLLI/SRLI/SRAI` shamt
  width (6 bits vs. 5) — ~2 days.
- CSR + S-mode (`csr.spl`/`csr_s.spl` inspiration): MXLEN/SXLEN=64 fields,
  already partially landed for rv64 QEMU/GHDL sim per S-mode delegation
  (3b36b68cd11) — ~3-5 days to port the *hardware* (not software-model) CSR
  file.
- MMU (Sv39): genuinely new hardware relative to rv32 (which has no MMU
  template at all in the K26-proven core) — page-table walker, TLB — this is
  the single biggest net-new block, ~2-3 weeks for a minimal single-entry-TLB
  walker.
- Mul/Div (M) + Atomics (A): RV64 needs 64-bit multiply/divide and `*W` AMO
  variants; rv32 already proved a divider on hardware (a9a344e9, divider
  writeback hazard fixed) — extending width is mechanical, new `*W` ops are
  not — ~1 week combined.
- Peripherals (clint/plic/uart/ram/bootrom/wb_interconnect): the rv64 driver's
  existing `gen_*_stub()` functions are a reasonable starting shape (they
  compiled/existed before this lane touched anything) but have never been
  GHDL-analyzed as a group (blocked by §3.1) — budget ~2-3 days to validate
  and wire once the core exists.

**Rough total for a hand-authored rv64 core template at rv32's proof rigor:
5-7 weeks of engineering**, dominated by the Sv39 MMU (new) and CSR S-mode
hardware port (nontrivial, not mechanical).

### Is the banked rv32 core extendable to XLEN=64 instead of writing fresh?

BB's extraction plan (`riscv_common_extraction_plan_2026-07-22.md`, §W3) is
directly relevant: it already generalizes decode/ALU/regfile logic behind an
`Xlen` parameter for the *software model*. If that extraction lands with a
genuine `Xlen`-parametric core, the *VHDL template* could plausibly be
generated by parameterizing `rv32_exec_core.vhd`'s width-dependent constants
(`RAM_ADDR_BITS`-style generics already exist for RAM sizing) rather than
writing rv64 from scratch — **but only for the mechanical parts** (regfile,
ALU width, decode immediate width). The MMU and CSR S-mode hardware are net
-new regardless of which core the datapath is banked from, since rv32's
proven template has no MMU at all. Recommendation: **extend, don't rewrite**,
once §W3 lands, but budget the MMU/CSR work as net-new either way — it does
not shrink from reusing the rv32 banked datapath.

## 5. Ordered lanes to a K26 rv64 bitstream

1. **Fix `OP_MISC_MEM` export** in `rv64gc_rtl/pkg.spl` (§3.3) — trivial,
   1-line fix, unblocks `core.spl`'s semantic compile (does not by itself fix
   VHDL codegen, since `core.spl` still has 0 `@hardware` annotations — see
   next item).
2. **File the phantom-API bug** for `compile_to_vhdl_module` (§3.1) — either
   implement it as a thin wrapper around `bin/simple compile --backend=vhdl`
   (mirroring what rv32's driver does via direct CLI invocation, not an
   in-process library call), or delete the 11-module loop from
   `rv64_vhdl_driver.spl` entirely if the template route (below) supersedes
   it. Recommend the latter given §4's conclusion — don't invest in fixing a
   codegen path that rv32 also never made to work.
3. **Author the rv64 GHDL-sim-only SoC top peripherals**
   (`clint.vhd`, `plic.vhd`, `uart.vhd`, `ram.vhd`, `bootrom.vhd`,
   `wb_interconnect.vhd`) by hand or by fixing the existing `gen_*_stub()`
   generators in the driver so they at minimum produce something
   GHDL-analyzable together with `soc_top_rv64.vhd` — this is the fastest
   path to *any* green GHDL analysis for rv64, independent of a real CPU core,
   and validates the SoC shell/bus wiring in isolation.
4. **Author `rv64gc_core.vhd`** as a hand template (§4 estimate: 5-7 weeks),
   starting from `rv32_exec_core.vhd` for the mechanical width/ALU/decode
   parts, with the Sv39 MMU and 64-bit CSR/S-mode hardware as the two
   dominant net-new blocks. Land incrementally: RV64I-only core first (GHDL
   -analyzable, boots nothing), then M/A extensions, then Sv39 MMU last (only
   needed for real Linux boot, not for a UART "hello" proof).
5. **`ghdl -a` the full set**, then `ghdl -e`/simulate a UART "hello" smoke
   before touching Vivado at all — this is the same order rv32 proved things
   in (GHDL sim before synthesis, synthesis before board).
6. **Vivado synth-only trial** (`-mode batch -source ... synth_design`, no
   `impl_design`/bitstream) once GHDL simulation passes, to get a real LUT/BRAM
   number instead of the estimate in §6. Gate on `pgrep -fc 'lnx64.o/vivado'
   == 0` first (checked clean this session — the one process match was
   `pgrep` matching its own argv, not a live Vivado run).
7. **Full impl + bitstream + K26 board bring-up**, following rv32's proven
   sequence (timing closure via `create_clock` on the CFGMCLK/STARTUPE3 path,
   fail-closed on negative WNS, board-serial proof) — only after 1-6.

## 6. Resource estimate vs. xck26

RV32 baseline (8ef2719412e, real synthesis+route result): **13.3% LUT, 26%
BRAM** on xck26.

No rv64 core has ever been synthesized (§3 shows generation itself is
blocked, so there is nothing to run Vivado synth on yet — this is an estimate,
not a measurement, and should be labeled as such wherever it is cited):

- **LUT**: RV64's datapath roughly doubles register/ALU/immediate width
  (32→64 bit) relative to rv32, and adds the Sv39 MMU (page-table walker +
  TLB, which has no rv32 analog to compare against) and wider CSR file.
  Estimate **26-35% LUT** (roughly 2-2.6x rv32, driven by width doubling
  plus the net-new MMU logic, not a clean 2x).
- **BRAM**: depends mostly on program/RAM sizing choices (preload size,
  TLB storage), which are independent of XLEN and not yet decided for rv64.
  Estimate **26-32% BRAM** — likely similar to rv32 unless the rv64 Linux
  payload requires materially larger on-chip RAM than rv32's, in which case
  this could exceed 32%.
- xck26 headroom (100% minus rv32's usage) comfortably covers either
  estimate; the risk is timing closure at the wider datapath, not
  overall resource exhaustion.

## 7. Gate evidence (this session)

- `scripts/fpga/generate_rv64_vhdl.shs` (rewritten, this lane): runs the
  driver, checks all 19 expected `.vhd` files by name (not just a raw count),
  runs `ghdl -a --std=08` per file, and always ends in exactly one of
  `RV64_VHDL_GEN: PASS` or `RV64_VHDL_GEN: BLOCKED` with an itemized reason
  list. Current real output on this worktree (`f4a2165f389`):

  ```
  RV64_VHDL_GEN: BLOCKED
    - driver (rv64_vhdl_driver.spl) failed: driver exited 139 with no 'error' line — ...
    - missing expected VHDL files (18/20): pkg.vhd alu.vhd regfile.vhd csr_s.vhd csr.vhd decode.vhd lsu.vhd mmu_sv39.vhd mul_div.vhd atomics.vhd trap.vhd rv64gc_core.vhd clint.vhd plic.vhd uart.vhd ram.vhd bootrom.vhd wb_interconnect.vhd
    - ghdl -a --std=08 failed on: soc_top_rv64: build/vhdl/rv64/soc_top_rv64.vhd:65:31:error: unit "rv64gc_core" not found in library "work"
  ```
  exit code 1.
- `pgrep -fc 'lnx64.o/vivado'` returned 1 in this session, but `pgrep -fa`
  confirmed the sole match was `pgrep` matching its own argv (self-match
  landmine, see `feedback_self_matching_pgrep_waiters.md`) — no live Vivado
  process. Machine was free; no Vivado trial was run this lane (nothing to
  synthesize yet — §3 shows generation itself is blocked before any file
  worth synthesizing exists).

## 8. Recommended next lane

Lane order 1-2 from §5 (fix `OP_MISC_MEM` export + resolve/remove the
phantom `compile_to_vhdl_module` reference) is a half-day fix that at least
gets the driver running end-to-end and the two already-working `.vhd` files
plus whatever the stub generators produce into a GHDL-analyzable state. The
real work — and the next *substantial* lane — is §5 item 4: hand-author
`rv64gc_core.vhd`, budgeted at 5-7 weeks, gated on BB's `Xlen`-parametric
extraction (§4) landing first so the mechanical width/ALU/decode portions can
be banked from rv32 rather than written twice.
