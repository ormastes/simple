# Bug: Free-function generic `T?` return wraps values in `Option::Some`

**Date:** 2026-06-26  
**Severity:** P2 — affects usability of generic helper free functions  
**Status:** Workaround applied; interpreter fix pending

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
