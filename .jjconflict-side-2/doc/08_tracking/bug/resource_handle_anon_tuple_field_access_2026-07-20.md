# HandleArena spec fails on anonymous-tuple `.0`/`.1` field access

**Date:** 2026-07-20
**Category:** GENUINE-BUG (likely interpreter/compiler tuple-return defect, not a lib API gap)
**Spec:** `test/unit/lib/engine/resource_handle_spec.spl` (2/8 passing)
**Command:** `SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/unit/lib/engine/resource_handle_spec.spl --no-session-daemon`

## Symptom

Unlike every other spec in this cluster, `src/lib/nogc_sync_mut/engine/
resource/handle.spl`'s `HandleArena<T>` is a **complete, correct**
implementation — `new()`, `insert()`, `get()`, `contains()`, `remove()`,
`len()`, `is_empty()`, `clear()` all exist and match the spec's usage
exactly. Yet 6 of 8 examples fail. The 2 that pass
(`returns nil for invalid index`, `returns nil for out-of-range index`) are
exactly the ones that never destructure the handle returned by `insert()`;
every failing example does `val idx = handle.0` / `val gen_val = handle.1`
on the anonymous-tuple return type of `me insert(value: T) -> (i64, i64)`.

## Root-cause hypothesis

This looks like the same class of anonymous/labeled-tuple return-value
handling defect already being worked on elsewhere in this codebase this
session (see recent commit `50c3393119e "fix(io_runtime): label process_run
return tuple ... root-fixes standalone-compile tuple-ambiguity for all ~150
callers"` and the `MEMORY.md` note "anon-tuple-return garbage (use struct)").
That fix targeted a *labeled* tuple return; `HandleArena.insert()` returns a
genuinely anonymous `(i64, i64)`, and `.0`/`.1` positional field access on it
under the `simple test` evaluator appears to misbehave (either yielding
garbage or throwing), even though the same code path presumably works fine
under `bin/simple run` for simple cases per the general tuple landmine
pattern. Not independently re-verified against `run` here due to time
budget — flagging the correlation (100% of failures touch `.0`/`.1` on this
tuple, 100% of passes don't) as strong enough to warrant investigation
without further guessing at exact interpreter internals.

## Why this isn't fixed here

`handle.spl`'s API is already correct and idiomatic (returns `(i64, i64)` —
a completely reasonable signature). This is not a spec or src rename issue;
it needs interpreter/compiler-level investigation into anonymous tuple
`.0`/`.1` access under the `simple test` evaluation path, which is out of
scope for this cluster-fix pass (guide: "Do NOT attempt a Rust seed source
fix; out of scope").
