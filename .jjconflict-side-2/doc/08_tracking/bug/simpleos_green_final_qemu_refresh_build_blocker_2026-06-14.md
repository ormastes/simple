# SimpleOS Green Final QEMU Refresh Blocker - 2026-06-14

Status: CLOSED on 2026-06-14.

## Summary

The opt-in SimpleOS final AP ring/user proof failed to refresh on the
`/tmp/simple-pherallel-continue-jj` host/toolchain even with the Simple test
runner timeout raised to 240 seconds. The blocker was closed after rebasing the
separate `/tmp/simple-pherallel-loop-jj` workspace on `main@origin`.

The command:

```sh
SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean --timeout 240
```

completed without the 120s runner timeout but failed one scenario before fresh
`HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, or `USER_SYSCALL_PASS=true`
evidence was produced.

The closing command:

```sh
SIMPLEOS_QEMU_SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean --timeout 260
```

passed 3 scenarios in 74244ms from `/tmp/simple-pherallel-loop-jj`.

Updated direct build classification after the x86_64 freestanding runtime ABI,
boot-entry, and final-handoff fixes:

- `--backend cranelift` now links
  `build/os/simpleos_green_carrier_probe.elf` from the current
  `/tmp/simple-pherallel-loop-jj` worktree. The fixed x86_64 boot runtime
  exports `rt_string_char_code_at`, `rt_for_iterable`, and no-op
  `rt_pool_safepoint` for compiler-inserted freestanding loop safepoints.
- The freestanding linker now preserves the boot object's `_entry32` ELF entry
  instead of overriding it with the Simple `spl_start` alias. `readelf` reports
  `Entry point address: 0x10001c`, matching `_entry32`; `spl_start` remains a
  separate alias to the Simple entry.
- Direct QEMU boot of that ELF with the spec's serial command reaches
  `[BOOT32]`, `[BOOT64]`, `[smp] AP reached 64-bit entry`,
  `[green-carrier-qemu] PASS=true`, `[green-carrier-qemu] PREEMPT_PASS=true`,
  `[green-carrier-qemu] SCHED_HANDOFF_PASS=true`, and
  `[green-carrier-qemu] USER_CR3_READY=true`.
- The non-final live SSpec wrapper also passes when pinned to the rebuilt
  compiler with `SIMPLEOS_QEMU_SIMPLE_BIN=src/compiler_rust/target/debug/simple`
  and `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1`; the latest run passed 3 scenarios
  in 64532ms.
- QEMU interrupt diagnostics showed the remaining direct-boot failure was an
  external interrupt immediately after `iretq` into the minimal final-probe
  CR3. The probe-only `set_user_task_address_space_for_probe` handoff now
  clears IF while keeping IOPL=3, allowing the ring-3 payload to emit COM1
  markers and return through syscall 60 before spinning.
- The direct boot now produces fresh
  `[green-carrier-qemu] HW_HANDOFF_PASS=true`,
  `[green-carrier-qemu] USER_ENTRY_PASS=true`, and
  `[green-carrier-qemu] USER_SYSCALL_PASS=true` marker evidence.
- `--backend llvm` is unavailable in the current `src/compiler_rust/target/debug/simple`
  driver build.

## Current Release Boundary

The release-visible SimpleOS handoff guard remains:

```sh
src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl --mode=interpreter --clean
```

That fast contract keeps the live QEMU marker triplet visible, keeps the
scheduler-only live lane separate from final AP ring/user proof, and records
that fresh final proof remains opt-in rather than part of ordinary release
smoke.

## Closure Criteria

- Keep the current-source Cranelift build of
  `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl`
  for `x86_64-unknown-none` passing.
- Fix the remaining direct QEMU boot/serial-marker failure. Done.
- Run the opt-in final QEMU lane successfully. Done.
- Capture fresh serial output containing all three final markers. Done:
  `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and
  `USER_SYSCALL_PASS=true`.
- Update `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` and
  `doc/09_report/README.md` to replace this blocker note with fresh PASS
  evidence. Done.
