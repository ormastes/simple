# Bootstrap used MSVC staticlib names for MinGW
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

Windows bootstrap always looked for `simple_native_all.lib` and
`simple_compiler_backfill.lib`. Cargo's MinGW staticlib convention is
`libsimple_native_all.a` and `libsimple_compiler_backfill.a`, so MinGW could
build the artifacts and then report them missing.

## Fix and prevention

The bootstrap archive prefix/suffix policy now follows the existing linker
flavor contract: an explicit linker flavor wins, then the canonical
`PLATFORM_ABI` incorporates `SIMPLE_WINDOWS_ABI` and recognized `MSYSTEM`
values, and plain Windows defaults to MSVC. One source regression pins both
Cargo naming forms, the override order, and the default.

No bootstrap/runtime execution is claimed under this session's static-only
restriction.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
