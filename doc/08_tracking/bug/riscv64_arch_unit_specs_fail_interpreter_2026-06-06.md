# RISC-V64 arch unit specs fail in interpreter mode

Status: open (triaged 2026-06-11)

Date: 2026-06-06

## Summary

The pure Simple RISC-V/SimpleOS stack gate specs pass, but lower-level RV64 arch
unit specs fail in interpreter mode. This blocks treating the RV64 arch-unit
lane as green evidence for stack hardening.

## Reproduction

```bash
bin/simple check test/03_system/os/simpleos_riscv_network_gate_spec.spl test/02_integration/http_baremetal_spec.spl test/01_unit/os/qemu_runner_extended_spec.spl test/01_unit/os/kernel/arch/riscv64_boot_spec.spl test/01_unit/os/kernel/arch/riscv64_interrupt_spec.spl test/01_unit/os/kernel/arch/riscv64_trap_frame_spec.spl test/01_unit/os/kernel/arch/riscv64_trap_model_spec.spl
bin/simple test test/01_unit/os/kernel/arch/riscv64_boot_spec.spl --mode=interpreter --json --timeout 120
bin/simple test test/01_unit/os/kernel/arch/riscv64_interrupt_spec.spl --mode=interpreter --json --timeout 120
bin/simple test test/01_unit/os/kernel/arch/riscv64_trap_model_spec.spl --mode=interpreter --json --timeout 120
```

## Observed

- `riscv64_boot_spec.spl`: 0 passed, 3 failed.
- `riscv64_interrupt_spec.spl`: 1 passed, 8 failed.
- `riscv64_trap_model_spec.spl`: 5 passed, 1 failed.

Failing summary rows from `build/test-artifacts/unit/os/kernel/arch/` include:

- `rv64 boot bootstrap trap runtime > records boot arguments`
- `rv64 boot bootstrap trap runtime > keeps boot argument capture independent from trap runtime setup`
- `rv64 boot bootstrap trap runtime > keeps the fixed kernel load address`
- `rv64 interrupt runtime bridge > dispatches a user ecall through installed runtime objects`
- `rv64 interrupt runtime bridge > rejects unsupported supervisor ecalls`
- `rv64 interrupt runtime bridge > records trap failures in the installed kernel log`
- `rv64 interrupt runtime bridge > updates a trap frame in place through the pointer bridge`
- `rv64 trap model > classifies supervisor timer interrupts`

## Passing Related Evidence

- `simpleos_riscv_network_gate_spec.spl`: 21 passed, 0 failed.
- `http_baremetal_spec.spl`: 7 passed, 0 failed.
- `qemu_runner_extended_spec.spl`: 26 passed, 0 failed.
- `riscv64_trap_frame_spec.spl`: 4 passed, 0 failed.

## Notes

No QEMU was launched for this reproduction. Several unrelated QEMU processes
were already running before the lane started.
