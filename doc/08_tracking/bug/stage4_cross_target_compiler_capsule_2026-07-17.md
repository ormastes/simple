# Stage4 accepted cross targets without cross compiler capsules

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

The hosted C plan can legitimately select Linux AArch64 or RISC-V64 cross C
drivers for ordinary native builds. Strict Stage4 reused that path even though
its compiler/backfill capsule is host-architecture-specific. Continuing toward
composition would mix cross-target Simple/runtime objects with a host compiler
capsule.

## Fix and prevention

Strict Stage4 now rejects `hosted_plan.requires_cross` after hosted target and
host-linker admission but before compiler discovery or temporary object
creation. Ordinary LLVM and Cranelift cross builds remain unchanged. The
focused source-order regression pins the guard before compiler, runtime, and
entry compilation; native target rows cover Linux x64/AArch64/RISC-V64, macOS
x64/AArch64, Windows x64, and FreeBSD x64/AArch64.

Real cross-target Stage4 remains deferred until target-specific compiler
capsules have explicit ABI, inventory, and distribution ownership. No runtime
execution is claimed under this session's static-only restriction.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
