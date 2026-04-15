# Audit: Remote Baremetal Execution

**Date:** 2026-04-04
**Feature:** Remote compile-upload-execute-collect pipeline for baremetal targets

## Implemented Core

Complete pipeline in `src/lib/nogc_sync_mut/debug/remote/exec/` via `RemoteExecutionManager`. Six target adapters:

1. **QemuRv32Adapter** -- QEMU RISC-V 32 via GDB-MI (`adapter_qemu_rv32.spl`)
2. **QemuArmAdapter** -- QEMU ARM Cortex-M via GDB-MI (`adapter_qemu_arm.spl`)
3. **GhdlRv32Adapter** -- GHDL VHDL-simulated RV32 via GDB stub (`adapter_ghdl_rv32.spl`)
4. **Ch32V307Adapter** -- Real CH32V307 hardware via `wlink` CLI (`adapter_ch32v307.spl`)
5. **Stm32H7Adapter** -- Real STM32H7 via OpenOCD telnet (`adapter_stm32h7.spl`)
6. **Trace32Adapter** -- TRACE32 PowerView via T32 GDB bridge (`adapter_trace32.spl`)

**Build system:** `src/compiler/80.driver/build/baremetal.spl` -- ARM, x86_64, RISC-V with arch-specific crt0.s, linker scripts, LLVM cross-compilation.
**Assembly startup:** `src/runtime/startup/baremetal/{riscv32,riscv64,x86,x86_64,arm32,arm64}/start.S`

## Lane Matrix

| Target | Method | Proof Status |
|--------|--------|-------------|
| RV32 / QEMU | Semihost ELF | **Stable** -- live QEMU verified |
| RV32 / QEMU | Raw GDB injection | **Regression lane** -- separate spec |
| ARM / QEMU | GDB-MI injection | **Implemented** -- connection_matrix tested (4 pass) |
| x86_64 / QEMU | Multiboot2 | **Implemented** -- boot spec (6 pass) |
| RV32 / GHDL | VHDL simulation + GDB stub | **Implemented** -- semihost ELF verified 2026-03-31; mailbox lane open |
| CH32V307 / wlink | Real hardware | **Board-dependent, proven** -- live `wlink status` + JIT execution verified 2026-03-31 |
| STM32H7 / OpenOCD | Real hardware telnet | **Board-dependent** -- adapter wired, E2E spec exists; skips when absent |
| STM32H7 / TRACE32 | T32 GDB bridge | **Board + license dependent** -- E2E spec exists; skips when absent |
| ZedBoard / FPGA | Zynq-7020 JTAG | **In progress** -- VHDL validated, JTAG chain not connected |

## Known Limits

1. **All test summaries show `duration_ms: 0`** -- interpreter mode verifies parse/load only; real execution requires compiled mode
2. **Every lane requires external tooling** -- QEMU lanes need `qemu-system-{arch}`, hardware lanes need probes + physical boards
3. **Hardware adapters skip cleanly** -- emit `[skip]` when prerequisites absent; no false passes
4. **GHDL lane partial** -- only semihost ELF works; mailbox lane and Simple-defined RV32 hardware flow remain open
5. **ZedBoard/FPGA incomplete** -- VHDL validated but JTAG chain not established (as of 2026-03-23)

## Proof References

**Source:** `src/lib/nogc_sync_mut/debug/remote/exec/` (6 adapters + manager), `connection_matrix.spl`, `src/compiler/80.driver/build/baremetal.spl`, `src/runtime/startup/baremetal/` (6 arch)
**Tests:** `qemu_rv32_jit_e2e_spec.spl`, `trace32_stm32h7_jit_e2e_spec.spl`, `ch32v307_jit_e2e_spec.spl`, connection_matrix (4 pass), semihost (11 pass), remote_baremetal_qemu (4 pass)
**Verification reports:** `doc/09_report/2026/03/remote_baremetal_completion_verification_2026-03-31.md` (PASS), `vhdl_backend_riscv_remote_interpreter_verification_2026-03-31.md` (PASS)
**Docs:** `doc/07_guide/backend/baremetal.md`, `doc/04_architecture/bare_metal_integration.md`

## Recommended README Wording

> **Bare-metal and remote execution** -- Cross-compile to ARM, RISC-V, and x86_64 baremetal targets with integrated QEMU testing; remote JIT execution via GDB-MI (QEMU), OpenOCD (STM32), `wlink` (CH32V307), GHDL (VHDL simulation), and TRACE32 adapters -- hardware lanes skip cleanly when probes or boards are absent
