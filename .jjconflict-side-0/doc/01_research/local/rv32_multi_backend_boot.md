<!-- codex-research -->
# RV32 Multi-Backend Boot — Local Research

**Feature:** `rv32_multi_backend_boot`
**Date:** 2026-04-02
**Status:** Draft

## Scope

This note records the current repo truth for three RV32 lanes that are easy to confuse:

- QEMU SimpleOS boot
- GHDL RV32 remote execution
- `examples/mllvm_qemu_rtl` hybrid/RTL simulation

The feature goal is not to invent a new backend. It is to document and then tighten the proof boundary across the lanes that already exist.

## Findings

### QEMU RV32 boot is real

- `src/os/qemu_runner.spl` already targets `Architecture.Riscv32` with `qemu-system-riscv32`, `virt`, `rv32`, and `build/os/simpleos_riscv32.elf`.
- `src/os/kernel/arch/riscv32/boot.spl` is a real OpenSBI/QEMU `virt` boot layer.
- The current smoke test, `test/qemu/os/boot/riscv32_boot_qemu_spec.spl`, checks for banner and boot markers.
- The current proof is early boot, not full OS feature coverage.

### GHDL RV32 is a remote execution lane, not an OS boot lane

- `src/lib/nogc_sync_mut/debug/remote/exec/adapter_ghdl_rv32.spl` and `test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl` prove that RV32 payloads can run under GHDL-backed execution plumbing.
- The current contract is remote payload execution through the shared JIT/composite path.
- The repository does not currently show a mailbox-backed RV32 OS boot lane in GHDL.

### `examples/mllvm_qemu_rtl` is model-level RV32 work

- `examples/mllvm_qemu_rtl/src/timing/hybrid_sim.spl` loads raw bytes at `0x80000000`; it does not implement a real ELF loader or board boot flow.
- `examples/mllvm_qemu_rtl/src/rtl/sim_engine.spl` mirrors architectural state into a signal store; it is not an executable RV32 CPU core.
- `examples/mllvm_qemu_rtl/tools/rtk_verilator_runner.sh` special-cases the stub RTL and falls back to lint-only behavior for the non-stub path.
- The existing integration specs prove timing, trace, and signal plumbing, not a bootable operating system image.

## Conclusion

The defensible current claim is:

- QEMU boots SimpleOS RV32 far enough to reach the serial boot markers.
- GHDL runs RV32 remote payloads through the shared remote execution lane.
- The hybrid/RTL example is not yet an OS boot proof and should not be documented as one.

