# Simple-core discriminant equality uses tagged-value comparison
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

SimpleOS filesystem compilation faults while mapping the Unit MIR type. Unit's
enum discriminant hash is the odd integer `0x183f6f19`.

## Root cause

Pure-Simple `rt_enum_check_discriminant(i64, i64)` used `==`. The generated
SimpleOS code routed that typed integer comparison through `rt_native_eq`, whose
tag heuristic treats odd integers above `0x1000` as heap pointers. It therefore
dereferenced `0x183f6f18` and faulted. `rt_is_none` had the same unsafe pattern
for its fixed enum discriminant.

## Owner fix

`src/runtime/simple_core/core_values.spl` compares discriminants with numeric
ordering (`<`/`>`) and treats neither-less-nor-greater as equal. This preserves
integer semantics without generic tagged-value comparison.

## Regression gate

Build the Simple-core archive, link the SimpleOS compiler, and require the
disassembly of `rt_enum_check_discriminant` and the discriminant branch of
`rt_is_none` to contain no call/reference to `rt_native_eq`. Then rerun the
filesystem `emit-llvm` profile and require translation to advance beyond the
third `__simple_main` local.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
