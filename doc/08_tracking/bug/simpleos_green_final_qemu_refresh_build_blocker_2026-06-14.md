# SimpleOS Green Final QEMU Refresh Blocker - 2026-06-14

Status: OPEN.

## Summary

The opt-in SimpleOS final AP ring/user proof cannot be refreshed on the current
`/tmp/simple-pherallel-continue-jj` host/toolchain even with the Simple test
runner timeout raised to 240 seconds.

The command:

```sh
SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean --timeout 240
```

completed without the 120s runner timeout but failed one scenario before fresh
`HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, or `USER_SYSCALL_PASS=true`
evidence was produced.

Updated direct build classification after the x86_64 freestanding runtime ABI
and boot-entry fixes:

- `--backend cranelift` now links
  `build/os/simpleos_green_carrier_probe.elf` from the current `/tmp/simple-pherallel-continue-jj`
  worktree. The fixed x86_64 boot runtime exports `rt_string_char_code_at` and
  `rt_for_iterable`.
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
- The direct boot still does not produce fresh
  `[green-carrier-qemu] HW_HANDOFF_PASS=true`,
  `[green-carrier-qemu] USER_ENTRY_PASS=true`, or
  `[green-carrier-qemu] USER_SYSCALL_PASS=true` marker evidence.
- `--backend llvm` is unavailable in the current `src/compiler_rust/target/debug/simple`
  driver build.

## Current Release Boundary

The release-visible SimpleOS handoff guard remains:

```sh
src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl --mode=interpreter --clean
```

That fast contract keeps the previous live QEMU marker triplet visible, keeps
the scheduler-only live lane separate from final AP ring/user proof, and records
that the old live PASS is historical opt-in evidence rather than a fresh current
rerun.

## Closure Criteria

- Keep the current-source Cranelift build of
  `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl`
  for `x86_64-unknown-none` passing.
- Fix the remaining direct QEMU boot/serial-marker failure.
- Run the opt-in final QEMU lane successfully.
- Capture fresh serial output containing all three final markers:
  `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and
  `USER_SYSCALL_PASS=true`.
- Update `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` and
  `doc/09_report/README.md` to replace this blocker note with fresh PASS
  evidence.
