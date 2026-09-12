# HandleArena spec fails on anonymous-tuple `.0`/`.1` field access
**Status:** RESOLVED (2026-09-12) — spec fixed, 8/8 green; the reported anonymous-tuple `.0`/`.1` defect no longer reproduces

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

## Triage 2026-09-12
Rule B: ran `bin/simple test test/unit/lib/engine/resource_handle_spec.spl` on the deployed seed; 3 of 8 checks still fail, so this record still reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-12 (BUGFIX-5)

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(Rust bootstrap seed, sha256 `3d120a6f`), worktree `/home/yoon/dev/simple-bugfix-5`
at base `89c5e3f865d`.

RED (before):
```
$ bin/simple test test/unit/lib/engine/resource_handle_spec.spl --no-session-daemon
SPEC FILE VERDICT: ... outcome=ERROR declared>=8 executed=8 passed=5 failed=3 skipped=0 dropped=0
```

**The original diagnosis is refuted.** Every example that destructures the
anonymous `(i64, i64)` tuple returned by `HandleArena.insert()` — `handle.0` /
`handle.1` — now PASSES. The 3 remaining failures were the exact complement:
`returns nil for invalid index`, `returns nil for out-of-range index`,
`old handle returns nil after slot reuse` — the three examples that never touch
`.0`/`.1`. They failed as *vacuous expects*:

```
✗ returns nil for invalid index
  vacuous expect: expect(Option::None) was never consumed by a matcher
  (2 non-bool expect(s), 1 matcher(s) ran).
```

Cause: the spec wrote `expect(result).to_be_nil` as a bare property. The matcher
is a call — `expect(x).to_be_nil()` (`test/README.md:145`, and every other spec
in the tree uses parentheses). A property tail asserts nothing, and the harness's
vacuity guard correctly failed it rather than passing silently.

Fix: `.to_be_nil` -> `.to_be_nil()` at 4 sites, applied identically to both
tracked copies of the spec (`test/unit/...` and `test/01_unit/...`, which were
byte-identical before and after, so no new test-tree divergence).

GREEN (after):
```
SPEC FILE VERDICT: test/unit/lib/engine/resource_handle_spec.spl    outcome=OK declared>=8 executed=8 passed=8 failed=0 skipped=0 dropped=0
SPEC FILE VERDICT: test/01_unit/lib/engine/resource_handle_spec.spl outcome=OK declared>=8 executed=8 passed=8 failed=0 skipped=0 dropped=0
```

No change to `src/lib/nogc_sync_mut/engine/resource/handle.spl` was needed; the
implementation was correct as the record already said.

- Status: RESOLVED (2026-09-12) — 80553f06c63, spec test/01_unit/lib/engine/resource_handle_spec.spl (+ test/unit mirror)
