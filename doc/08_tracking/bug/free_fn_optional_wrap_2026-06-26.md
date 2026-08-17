# Bug: Free-function generic `T?` return wraps values in `Option::Some`

**Date:** 2026-06-26  
**Severity:** P2 — affects usability of generic helper free functions  
**Status:** REOPENED 2026-08-17 — the 2026-08-17 "already-fixed" re-verification
ran on an UNPINNED engine and therefore measured only the interpreter arm. With
the engine pinned, the JIT arm is wrong. (~~RESOLVED — ALREADY-FIXED,
re-verified 2026-08-17.~~)

## Measured arms 2026-08-17 (engine PINNED, both arms executed)

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
59536728 bytes, mtime 2026-08-16 22:59:37.799277177 +0000 (stale Rust seed).
No rebuild, no redeploy. `rc` read from a variable on the line AFTER the
command, never through a pipe.

Probe — the doc's own reproducer, moved inside a `fn` and carrying the in-`fn`
2^60 JIT-compilation control (a top-level body runs interpreted regardless of
the pin):

```
struct Box<T>:
    item: T
fn box_get<T>(b: Box<T>) -> T?:
    b.item
fn main():
    print("v=" + box_get(Box(item: 42)).to_string())
    val p60 = 1152921504606846976
    print("pow=" + p60.to_string())
```

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run q05_freefnopt.spl   # rc=0
v=42
pow=1152921504606846976

$ SIMPLE_EXECUTION_MODE=jit bin/simple run q05_freefnopt.spl           # rc=0
v=0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002
pow=-1152921504606846976
```

Expected `v=42`. The negated `pow` proves the JIT arm actually compiled. Both
arms rc=0 — a wrong value, not a crash, so NOT an rc=143/137/144 UNVERIFIED.
The JIT arm prints the integer payload 42 reinterpreted as an f64 denormal
(2e-322 ≈ raw bits 42), i.e. the correct value is present and only the
tag/type recovery on the generic `T?` return is wrong. NOT ASSERTED: a shared
root cause with the other reopened rows — this row is recorded on its own
measurement only.

## Re-verification 2026-08-17 (partial-fix sweep, lane 1)

The doc's own reproducer, run verbatim on the deployed seed
(`bin/simple`, Rust seed dated 2026-08-16):

```
struct Box<T>:
    item: T
fn box_get<T>(b: Box<T>) -> T?:
    b.item
...
expect(box_get(Box(item: 42))).to_equal(42)

Results: 1 total, 1 passed, 0 failed
```

The free function returns the raw `42`, not `Option::Some(42)`. The interpreter
defect this file describes no longer reproduces.

STILL WORTH DOING (not done here, and NOT a defect): the `any`-typed
workarounds recorded under "Affected Files" -- `stack_get`/`queue_get` in
`src/lib/tooling/ds_utils.spl` -- can now be given their real `T?` return
types. That is a cleanup, not a bug; it is listed here so the workaround is not
forgotten now that its cause is gone.

NOT PROVED: the `Option::None`-vs-`nil` half of the filing (the "not found"
branches in `algorithm_utils.spl`) was not re-probed in this pass, nor was the
pure-Simple self-hosted lane.

--- original filing below, kept for history ---

**Status (original):** Workaround applied; interpreter fix pending

## Summary

In the seed interpreter (and STAGE4), a top-level free function with a generic
optional return type `T?` always wraps its return value in `Option::Some(value)`
instead of returning the raw value.  Returning `nil` produces `Option::None`
instead of actual nil.  `impl`-method `T?` returns are **not** affected — they
work correctly.

## Reproduction

```spl
struct Box<T>:
    item: T

impl Box<T>:
    fn get() -> T?:     # method — returns raw 42 ✓
        me.item

fn box_get<T>(b: Box<T>) -> T?:   # free fn — returns Option::Some(42) ✗
    b.item

val b = Box(item: 42)
expect(b.get()).to_equal(42)        # passes
expect(box_get(b)).to_equal(42)    # fails: expected Option::Some(42) to equal 42
```

## Affected Files

- `src/lib/tooling/ds_utils.spl` — `stack_get` and `queue_get` worked around
  with `any` return type (see ponytail comments in that file).
- `test/unit/lib/common/algorithm_utils_sort_search_spec.spl` (2026-07-20,
  whole-suite `lib/common` triage cluster) — 12/39 failures. All free
  functions in `src/lib/common/algorithm_utils.spl` returning `i64?`
  (`linear_search`, `binary_search`, `find_min`, `find_max`,
  `find_min_index`, `find_max_index`, `find_sublist`) hit this class under
  `bin/simple test`. Source is correct (`return nil` / bare `i64`, no
  explicit `Option::Some`/`Option::None` construction). Tried the mechanical
  `.?` → `!= nil` migration: the "found" cases then pass (34/39), but the
  "not found" cases still fail with `expected Option::None to not equal
  nil` — i.e. the wrapping is inconsistent per-branch (bare `nil` becomes
  boxed `Option::None` under `!=`, while `.?` on the same nil returns
  literal `nil` per the original failure `expected nil to equal false`).
  Left unmodified (reverted to original `.?` form) — not a stale-test issue,
  confirms this is the same free-function `T?` interpreter defect, not
  spec-fixable without the interpreter fix.
- `test/unit/lib/common/array_coverage_spec.spl` (2026-07-20, same triage
  cluster) — 10/227 failures, all `array_max`/`array_min` (free functions,
  `-> i64?`) cases where a value is found: `expected Option::Some(N) to
  equal N` (Pattern 1 — matches `ds_utils_t_optional_wrapping_inconsistency`
  exactly). Not touched; would require weakening `to_equal(N)` to accept a
  wrapped value to force green.
- `test/unit/lib/common/array_search_transform_spec.spl` (2026-07-20, same
  cluster) — 2/35 failures, same `expected Option::Some(N) to equal N`
  pattern on `array_max`/`array_min`-equivalent found-value cases.

## Workaround

Change affected free functions from `T?` to `any`.  The caller's `to_equal` and
`to_be_nil` matchers work correctly against `any`.  Loses static type info but
preserves runtime behaviour.

## Fix Location

Likely in the interpreter's function-return handling for generic optionals.
Compare `eval_fn_return` for methods vs free functions — the method path
correctly unwraps/passes through while the free-function path wraps in
`Option::Some`.

See `src/compiler_rust/` interpreter eval code.
