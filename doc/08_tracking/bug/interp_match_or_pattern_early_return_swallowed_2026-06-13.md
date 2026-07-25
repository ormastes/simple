# Interpreter: `return` inside if-block under or-pattern match arm is swallowed

**Date:** 2026-06-13
**Severity:** medium (silent wrong value, no error)
**Status:** FIXED 2026-06-13 — root cause found and fixed; regression tests added

## Symptom

A method whose `match` uses an or-pattern arm (`A | B:`) with a nested `if` +
`return` falls through to the post-match `return` even when the arm matched and
the `if` condition was true. No error; the function returns the wrong value.

## Repro (was live in src/lib/common/ui/profile.spl ProfileSet.resolve)

```simple
fn resolve(orientation: Orientation) -> WidgetNode:
    match orientation:
        Orientation.Landscape | Orientation.Square:
            if self.landscape_root != nil:
                return self.landscape_root      # swallowed — falls through
        Orientation.Portrait:
            if self.portrait_root != nil:
                return self.portrait_root       # swallowed — falls through
    return self.default_root                    # always taken
```

Observed via `test/01_unit/app/ui/profile_spec.spl` ("resolves landscape
profile when set" / "resolves portrait profile when set" / "resolves Square as
Landscape" — failed with "expected default to equal landscape" for months;
pre-existing before the 2026-06 mobile-gui-platform work).

## Workaround applied

Rewrote `ProfileSet.resolve` as plain `if`/`return` chains (profile.spl) —
spec went 51/54 → 54/54. `ProfileSet.has_profile` uses the same or-pattern
shape but returns the match arm value as an expression (no early `return`
inside `if`), which appears unaffected — not rewritten.

## Actual root cause (corrected from suspected)

The bug doc's original "suspected root cause" (or-pattern lowering) was wrong.
The true cause is in `exec_block_fn` (`interpreter/block_exec.rs`): when the
**last statement** of a block is a `Node::Match` or `Node::If`, the function
called `exec_match_expr`/`exec_if_expr` to capture the implicit return value.
Those "expr" variants convert `Control::Return(v)` to `Ok(v)` — they collapse
the early-return signal into a plain value. Result: the match arm's `return`
never reaches the enclosing function.

The same bug existed in `interpreter/expr/control.rs` (match-as-expression arm
evaluation, lines ~176-193) for the same reason.

**Affected shapes:** any `match` arm whose last statement is `if cond: return X`
or a nested `match: return X`, regardless of whether the arm pattern is an
or-pattern (`A | B:`) or a single pattern. The portrait arm in the original
repro (single-pattern) was equally broken — both or-pattern and single-pattern
return values were 0 before the fix.

**Why or-patterns appeared to be the culprit:** `ProfileSet.has_profile` (which
used or-patterns) happened to work because it returned the arm value as an
expression (no explicit `return` inside `if`). The broken cases all had the
`if cond: return X` shape as the arm's last statement.

## Fix (2026-06-13)

- `interpreter_control.rs`: made `exec_match_core` `pub(crate)` (was `fn`);
  added `exec_if_core` returning `(Control, Value)` which preserves
  `Control::Return/Break/Continue`; refactored `exec_if_expr` as a thin wrapper
  that collapses control for pure-expression callers.
- `interpreter/block_exec.rs`: updated `exec_block_fn` last-statement handling
  to call `exec_match_core`/`exec_if_core` and propagate non-`Next` control.
- `interpreter/expr/control.rs`: same fix for match-as-expression arm iteration.
- `interpreter/mod.rs`: re-exported `exec_if_core` and `exec_match_core`.

## Regression tests added

- Rust: 8 new tests in `src/compiler_rust/driver/tests/interpreter_advanced_features_tests.rs`
  covering: or-pattern both variants, single-pattern, arm-value-no-return,
  non-matching fallthrough, false-condition fallthrough, nested-match return.
- SPipe spec: `test/01_unit/compiler/interpreter/match_arm_early_return_spec.spl`

## Follow-up gaps

- The profile.spl workaround (plain if/return chains) was left in place — it
  still passes and reverting it to the match form is a separate optional cleanup.
- Guard clauses (`when cond:` form if any) and `break`/`continue` under the
  same pattern were not specifically tested; the control-flow path handles them
  via the same `other @ (Control::Return | Control::Break | Control::Continue)`
  match arm, so they should be correct — but no dedicated tests were added.
