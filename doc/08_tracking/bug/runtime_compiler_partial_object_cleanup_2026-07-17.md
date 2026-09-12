# Runtime compiler leaked partial object sets on early failure
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

`compile_runtime_objects` allocates deterministic temporary paths for the whole
runtime source list. A missing later source returned without deleting objects
already compiled earlier in the loop. The zero-object and partial-count
fail-closed returns also omitted cleanup.

## Fix and prevention

All post-plan failure returns now call the existing
`cleanup_runtime_objects(objects)` owner before returning. The focused source
regression in `runtime_compiler_spec.spl` pins all four post-plan exits: missing
source, compiler failure, zero compiled objects, and partial object count.

This fixes the shared hosted C-runtime compiler used by ordinary LLVM,
Cranelift, and Stage4. Runtime/native execution remains pending under this
session's explicit static-only restriction.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
