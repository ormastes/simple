# Simple RISC-V SoC + Linux Boot Feature Expert

## Role

Own process knowledge for the Simple-language RISC-V cores (rv32 + rv64), their
SoC integration, the XLEN-shared logic, JTAG/AOP debug, the 4 GiB address work,
the F/D FPU, and the state of booting Linux on them (model + FPGA). Written to
stop the recurring mistake of reading ONE legacy synthesizable `.vhd` and
concluding "nothing exists."

## Read-the-history-FIRST rule (why answers went wrong 2026-07-23)

Before answering ANY architectural "does X exist / can it boot" question about
RISC-V, consult, in order: (1) the recalled `MEMORY.md` project entries
(`project_riscv_unification_*`, `project_riscv_fpga_jtag_*`, `project_riscv_fpu_*`),
(2) this wiki + the research/plan docs below, (3) the probe suite in
`scripts/check/check-riscv-hardware-gates.shs` (each probe NAMES a capability),
THEN inspect code. The failure mode was inspecting `rv32_exec_core.vhd` (a
legacy hand-written 64 KB reference core) and generalizing "rv32 has no MMU / no
big address space" — false: the CURRENT `.spl` model has Sv32 + S-mode + 4 GiB.
Distinguish three layers every time: **legacy synthesizable `.vhd` reference**
vs **current `.spl` behavioral model** vs **synthesizable-RTL generation (a
placeholder stub today)**.

## Pipeline Links

- Unification decision doc:
  `doc/01_research/hardware/riscv/riscv32_riscv64_unification_realrtl_aop_jtag_2026-07-21.md`
  (one XLEN-parameterized core 85-95% shared; AOP only for hart hooks; fail-closed
  real-RTL qualification; profiles honest — `gc`/`*d` require real F/D).
- Plan: `doc/03_plan/hardware/riscv/riscv_unification_parallel_agent_plan_2026-07-21.md`;
  JTAG: `doc/03_plan/hardware/debug/riscv_jtag_debug_plan_2026-07-21.md`.
- Linux boot guide (authoritative state + reproduction):
  `doc/07_guide/os/rv64_soc_linux_boot.md`.

## Code Map

- **Shared XLEN layer** `src/lib/hardware/riscv_common/` — `xlen.spl`
  (`XlenConfig.rv32()/.rv64()`: mask/sign_bit/bytes_per_reg/cause_interrupt_bit),
  `alu.spl`, `decode.spl`, `rtl_decode.spl`, `csr_defs.spl`, `registers.spl`,
  `memory.spl`, `platform.spl`. BOTH cores import it; do NOT build a second common
  layer. Full single-core migration is deliberately NOT on the generic-function
  path yet (monomorphization unproven — templates must be fail-closed first).
- **rv32 core** `src/lib/hardware/rv32i_rtl/` — alu/csr/csr_s/decode/lsu/regfile/
  trap + **`mmu_sv32.spl`** (Sv32 MMU) + S-mode. 4 GiB addressing via
  `src/lib/hardware/soc_rtl/ram_sparse.spl` (sparse page-backed).
- **rv64 core** `src/lib/hardware/rv64gc_rtl/` — alu/atomics/csr/csr_s/decode/lsu/
  mmu/`mmu_sv39.spl`/mul_div/regfile/trap/**`fpu.spl`** (F/D, DI-toggle, landed
  2026-07-23, wired into `core.spl`: FP compute + load/store + fcsr CSR +
  mstatus.FS).
- **SoC** `src/lib/hardware/soc_rtl/` — `soc_top_64.spl` (bootrom→0x80000000, DRAM
  0x80000000, CLINT/PLIC/UART16550, Sv39, `soc_top_64_run` with OpenSBI
  checkpoints hit_a4/cc/fw), `ram64.spl`, `ram_sparse.spl`, `bootrom.spl`,
  `wb64_interconnect.spl`.
- **JTAG** `src/lib/hardware/debug/` (jtag_tap/riscv_dtm/dmi_bus/debug_module,
  GHDL tbs, IDCODE 0x15350067, Stages 1-3/5) + **AOP hart hooks**
  `src/lib/hardware/debug_hooks/hart_debug.spl` (repo `on pc{…} use … before`
  weave; `driver_pipeline.weave_aop` + `mir_aop_injection`). Also
  `src/lib/hardware/link_mux/` (frame/mux/jtag_route — shared-link channel mux;
  one link carries log+term+jtag). Verified 2026-07-24: `frame_probe` /
  `mux_probe` / `jtag_route_probe` ALL PASS interpreter+jit. The jtag channel
  tunnels OpenOCD `remote_bitbang`; Phase 1 reached IDCODE only — the DMI/DM
  extension (`jtag_debug_probe.spl`: halt / read-write GPR+dpc / resume against
  the rv64 core model over the muxed link) is the in-model debugger. Board
  path = BSCANE2 USER4 tunnel (`jtag_debug_chain.vhd` + `G_DEBUG_JTAG` guard,
  `openocd_kv260_bscan.cfg`, `check_kv260_jtag_debug.shs` verify/soak). THE
  debugging guide (both paths + troubleshooting):
  `doc/07_guide/hardware/fpga/simple_riscv_jtag_debugging.md`.
- **Synthesizable RTL** `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd`
  is the ONLY real synthesizable CPU (rv32, no MMU, reference/oracle). The
  `fpga_linux` bundle generator (`src/lib/hardware/fpga_linux/riscv_fpga_linux.spl`)
  emits `GENERATED_RTL_NOT_IMPLEMENTED` placeholders — NOT a working core.

## Sanity gates (probe = capability)

- `soc_top_64_probe` → `SOC64 PROBE: ALL PASS` (interpreter only — JIT boxed-int
  61-bit defect, `seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`).
- `addr4g_probe` → `ADDR4G_PROBE: ALL PASS` (4 GiB rv32 + rv64 ≥2^31).
- `check_linux_loading_rv32.shs` → `CHECK_LINUX_LOADING_RV32: PASS`.
- `check-riscv-hardware-gates.shs` — bundle (JTAG tbs + soc/core/mux/fpu probes;
  FP probes run interpreter via the `INTERP_PROBES` list).

## What is missing to boot Linux (honest)

- **rv64, `.spl` model:** Linux→/init proven on QEMU's OWN cpu with Simple's
  `soc_virt.dtb` (`build/os/rv64_soc/transcripts/qemu_ourdtb_wired.log`). On the
  Simple core, OpenSBI runs reloc→bss→fw_platform_init→C-init then **stalls
  spinning ~0x800005F4 before the banner** (open: SBI/timer or console bind).
  Full boot also needs the **JIT boxed-int fix** (interp ≈540 inst/s is too slow
  for billions of insns; JIT currently mis-executes the core).
- **rv32, `.spl` model:** MMU(Sv32)+S-mode+4 GiB exist; missing = a **bootable
  rv32 SoC-top** (only `soc_top_64` boots) + an rv32 Linux kernel build.
- **Either on FPGA:** synthesizable rv64 core EXISTS since 2026-07-24 —
  hand-written `examples/09_embedded/fpga_riscv/rtl/rv64_exec_core.vhd`
  (RV64IM+minimal Zicsr, M-mode, no MMU/FPU/C; sim gates green: GHDL smoke
  `RV64_UART_MARKER_SEEN`, Adler-32 soak golden == host == `.spl` model
  three-way, 20/20 directed DIV/REM/W-op edge cases) — **not yet board-proven**;
  Vivado synth via `build_k26_rv64.shs` + KV260 10-min soak pending. Linux on
  FPGA still needs MMU in RTL. Synthesizable rv32 `.vhd` lacks MMU/4 GiB; no
  `.spl`→Verilog backend (`generate_rv64_vhdl.shs` stays BLOCKED-honest for the
  generator path). Board present (KV260, FT4232H JTAG+UART, Vivado 2025.2).

## Landmines

- `unit` is a RESERVED type keyword (→ "found Dot"); never a var/field name.
- Hardware `.spl` runs INTERPRETER-only (JIT boxed-int + `spl_f64_to_bits`
  miscompile). Do not "fix" bare `len(x)`→`.len()` / bare `use path.sym`→brace in
  `ram64`/`wb64`/`core.spl` to enable JIT — it exposes the broken JIT core
  (soc/boot probes FAIL). Fix the JIT codegen first.
- WC caveat: leaked jj conflict markers fail the gates at parse time; restore with
  `git checkout origin/main -- src/lib/hardware/ examples/09_embedded/fpga_riscv/`.
- Runner (2026-07-24): the deployed CLI's in-process `run` cannot resolve
  `std.hardware.*` brace-imports (bug doc
  `native_cli_run_std_hardware_brace_import_unresolved_2026-07-24.md`). Run
  hardware probes via seed delegation
  (`SIMPLE_BOOTSTRAP_DRIVER=$PWD/src/compiler_rust/target/bootstrap/simple`)
  or a scratch-named CLI copy + `simple_seed` sibling (`wjob` pattern — also
  dodges earlyoom's kill-by-name on `simple`). A Jul-23 deploy clobbered
  `bin/release/<triple>/simple` with a compile-only bootstrap binary; if
  `bin/simple` suddenly has no `run` command, restore the full CLI (backup at
  `simple.bootstrap-clobber-bak`, known-good at `build/native_probe/simple`).
