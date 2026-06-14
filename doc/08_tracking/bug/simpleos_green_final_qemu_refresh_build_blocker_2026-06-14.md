# SimpleOS Green Final QEMU Refresh Build Blocker - 2026-06-14

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

Direct build classification:

- `--backend cranelift` reaches the freestanding linker but leaves
  `rt_string_char_code_at` and `rt_for_iterable` unresolved.
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

- Build `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl`
  for `x86_64-unknown-none` with the current-source compiler.
- Run the opt-in final QEMU lane successfully.
- Capture fresh serial output containing all three final markers:
  `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and
  `USER_SYSCALL_PASS=true`.
- Update `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` and
  `doc/09_report/README.md` to replace this blocker note with fresh PASS
  evidence.
