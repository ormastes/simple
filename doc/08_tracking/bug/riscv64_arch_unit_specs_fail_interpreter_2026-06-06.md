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

## Evidence 2026-11-05 (worktree work/libbug-linux-rv64specs-20261105, release/1.0.0 base)

Reproduced under interpreter mode (seed full CLI, aarch64 host). Verdicts on the
unmodified branch and after the fix:

| Spec | Before | After |
|------|--------|-------|
| riscv64_boot_spec.spl | 5 passed / 0 failed | 5 passed / 0 failed (unchanged) |
| riscv64_interrupt_spec.spl | 1 passed / 8 failed | 10 passed / 0 failed |
| riscv64_trap_frame_spec.spl | 4 passed / 0 failed | 4 passed / 0 failed (unchanged) |
| riscv64_trap_model_spec.spl | 4 passed / 2 failed | 6 passed / 0 failed |

Classification:

- riscv64_trap_model_spec.spl — SOURCE BUG. `RV64_SSTATUS_FS_MASK`,
  `RV64_SSTATUS_FS_INITIAL`, and `RV64_CONTEXT_BYTES` were missing from
  `src/os/kernel/arch/riscv64/trap_model.spl`, and the initial kernel/user
  sstatus values did not set FS=Initial (1 << 13). The pinned oracle values are
  independently corroborated by
  `test/01_unit/os/kernel/loader/riscv64_fs_exec_spawn_spec.spl:111-112`, which
  expects `val RV64_CONTEXT_BYTES: u64 = 544` and
  `val RV64_SSTATUS_FS_INITIAL: u64 = 1 << 13` in the trap_model source.
- riscv64_interrupt_spec.spl — SPEC BUG (missing fixture). Every install and
  dispatch path is guarded by `_rv64_is_trap_owner_hart()`
  (`src/os/kernel/arch/riscv64/interrupt.spl:146`), which requires the
  boot-sealed CPU identity snapshot published by real boot entries via
  `riscv_publish_boot_hart_identity_v1` (`src/os/kernel/arch/riscv64/boot.spl:90`).
  The specs never published it, so under the interpreter the current hart
  resolved to CPU_ID_UNRESOLVED and every guarded path refused with
  "rv64 trap reached non-owner hart". Fix: the spec now publishes the boot hart
  identity for the observed `read_tp()` value, mirroring the hardware boot
  path. The owner-hart guard itself is intentional design (see the comment at
  interrupt.spl:142-145) and was left intact.

No regressions: neighboring arch specs (x86_64_interrupt 8/2, x86_64_apic,
x86_32_trap_model, hal_riscv64_phase_a, riscv64_ipc_destroy_port,
riscv64_noalloc_pmm, riscv64_boot_tcp_policy, riscv64_freestanding_policy and
others) show byte-identical verdicts before and after the change; the remaining
failures among them pre-date this fix on release/1.0.0.
