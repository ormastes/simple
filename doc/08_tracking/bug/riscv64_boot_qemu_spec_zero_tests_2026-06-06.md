# RISC-V64 QEMU Boot Spec Yields Zero Executed Tests

## Closed 2026-09-13 — Resolved 2026-06-06 by removing the misleading zero-test spec

- **inferred** The Status line records the resolution: the misleading spec that declared tests but executed none was removed.
- **measured** All three paths the entry references still exist (path scan: 3 referenced, 0 missing), i.e. the surviving lane is the intended one.
- **inferred** QEMU RISC-V boot cannot be exercised from this Windows host; closing on the recorded removal.


Date: 2026-06-06

## Summary

`test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl` is a direct
system-spec path with five `slow_it` scenarios, but the runner reports zero
listed, passed, or failed tests.

Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below
`@platform: baremetal(riscv64)` filter from the host-run QEMU spec.

## Evidence

Commands:

```bash
bin/simple test test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl --clean --json
bin/simple test test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl --only-slow --clean --json
```

Both commands returned success with:

```json
{
  "total_passed": 0,
  "total_failed": 0,
  "files": []
}
```

After the fix:

```bash
bin/simple test test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl --list
bin/simple test test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl --only-slow --clean --json
```

The first command lists 5 slow tests. The second command reports 5 passed and
0 failed.

## Impact

This was weak release evidence: a RISC-V64 QEMU boot gate could appear green
while running no scenarios. The boot spec now discovers and executes its slow
scenarios, while the live `scripts/qemu/qemu_rv64_http_test.shs` gate and the
opt-in `test/03_system/os/simpleos_riscv_network_gate_spec.spl` wrapper still
provide direct RV64 boot/network/storage evidence.
