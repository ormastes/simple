# BLOCKER: no synthesizable rv64 core → Linux cannot run on the real FPGA

**Date:** 2026-07-23
**Severity:** blocker (board-runnable rule: "when board-run is genuinely blocked, say so explicitly and file it")
**Goal it blocks:** "run Linux on the real FPGA to harden Simple RISC-V 32/64"

## Definitive finding

Linux-on-real-FPGA is blocked for **both** lanes, at the RTL level — not a wiring
gap, a *missing-core* gap.

### rv32 — synthesizable core exists, but no MMU
- Real synthesizable HDL: `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd`
  + `soc_top_rv32.vhd` (hand-written VHDL, boots on K26).
- **Architectural stop:** rv32_exec_core has no MMU and ~64KB BRAM. Linux needs an
  MMU (Sv32) + tens of MB DRAM. This core cannot run Linux by design.

### rv64 — no synthesizable core exists at all
- `git ls-files '**/*.vhd' | grep rv64` → only `tb_rv64_wb_soc_smoke.vhd`
  (a **testbench**). There is **no** `rv64_exec_core.vhd`, no `soc_top_rv64.vhd`.
- The rv64 "core" exists **only as a Simple behavioral model**
  (`src/lib/hardware/rv64gc_rtl/*.spl`: alu/decode/lsu/mmu_sv39/mul_div/atomics/
  trap/csr/csr_s/regfile/core). This runs in the Simple interpreter/JIT as a
  **software simulator** — it is not HDL and is not synthesizable.

### The `fpga_linux` "generator" emits placeholders, not RTL
`src/lib/hardware/fpga_linux/riscv_fpga_linux.spl:854` `generated_core_vhdl()` does
**not** translate `.spl` → VHDL. It emits a stub whose architecture body is:

```vhdl
assert false report "GENERATED_RTL_NOT_IMPLEMENTED lane=..." severity failure;
```

with header `readiness: contract-not-ready ... reason: placeholder-core-no-semantic-rvfi`.
This is true for the rv32 *and* rv64 emitted cores. `write_generated_core_lane`
(same file) writes an empty package + this placeholder + testbenches. So the
"generated RTL bundle" is a **contract/scaffolding framework**, not a working core.

## What "run Linux on FPGA" actually requires (not achievable this session)
1. A **synthesizable rv64gc + Sv39 MMU core** in VHDL — either hand-written
   (multi-week verified RTL) or produced by a real `.spl`→synthesizable-VHDL HLS
   backend that does not exist (`generated_core_vhdl` is a stub).
2. A DRAM path (K26/KV260: PS DDR4 via AXI HPM master into PL).
3. A **physical board connected to this environment** — none is (no `hw_server`
   target) — plus a 3v3 PMOD console adapter (H12/E10).

## What IS real and hardenable now (this session's deliverable)
- The **rv64gc `.spl` behavioral model** + the **rv32_exec_core** VHDL both run and
  are stressed by the 10-minute hard soaks (`scripts/fpga/soak_rv64_hard_job.shs`,
  `soak_rv32_hard_job.shs`) — that is the executable form of "10-min hard works".
- Linux **does** boot rv64 under QEMU (`scripts/debug/debug_rv64_linux_gdb.shs`,
  RV64-LINUX-GDB-DEBUG: PASS) — same ISA the `.spl` model implements.

## Honest status line
- rv32 Linux on FPGA: **impossible** (no MMU) — architectural, filed here.
- rv64 Linux on FPGA: **blocked** — no synthesizable core exists; needs a new
  rv64gc+Sv39 RTL core (large) and a connected board (absent here).
- rv32/rv64 core-model **hardening + 10-min soak**: achievable and being run.
