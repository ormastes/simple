# Stage3 Ignores CPU Baseline and Emits BMI2

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

The stage3 pure-Simple native builder prints `unknown option '--cpu', ignoring`
for `--cpu x86-64-v1`, then Cranelift emits BMI2 `shlx`. The production QEMU
fixture originally used baseline `qemu64`, causing a `#UD` in PMM bitmap code.

The WM evidence fixture temporarily declares QEMU's `max` model after
`qemu64,+bmi2` still faulted on the emitted `shlx`. The compiler must accept and propagate the CPU baseline or
fail the build; silently ignoring it is not permitted. Once fixed, the fixture
should return to baseline `qemu64` and retain an instruction-set audit.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
