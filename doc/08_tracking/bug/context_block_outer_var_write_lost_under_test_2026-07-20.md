# `context <obj>:` block body writes to an outer `var` are lost under `test`

**Date:** 2026-07-20
**Component:** `bin/simple test` (SSpec evaluator) scoping for `context
<obj>: <body>` blocks (block-scoped method-context dispatch).
**Severity:** Medium — narrow construct (`context obj:` block bodies that
assign to an outer `var`), confirmed evaluator-specific (works correctly
under `bin/simple run`).

Same general "`test` evaluator diverges from `run`" landmine family as
`generic_class_static_method_unresolved_under_test_2026-07-20.md` and the
same broad shape as `while_val_pattern_binding_not_visible_in_body_2026-07-20.md`
— but a distinct mechanism (outer-`var` write from inside a `context` block
body is silently dropped, vs. a pattern-destructured binding being
unreadable inside a `while val` loop body). Also adjacent to, but distinct
from, `with_statement_exit_self_field_mutation_lost_2026-07-20.md` (same
"builtin control-construct swallows a mutation" shape, different construct:
`with...as` vs `context obj:`) and
`nested_fn_closure_mutation_not_propagated_2026-07-20.md` (general
by-value-closure-callback mutation loss) — unlike both of those, THIS
construct's mutation loss is confirmed evaluator-specific (`run` gets it
right, only `test` loses the write), which is new information not covered
by either restored doc, so filed separately rather than folded in.

## Symptom

```
dispatches method to context object
  expected 0 to equal 42
accesses self fields in context method
  expected 0 to equal 42
uses method_missing in context block
  expected 0 to equal 42
```

`var res = 0` declared before a `context <obj>: res = <method call>` block;
after the block, `res` is still `0` under `bin/simple test` — the
assignment inside the `context` block body never reaches the outer `res`.

## Minimal repro — diverges between `run` (works) and `test` (fails)

```simple
class Calculator:
    fn double(self, x):
        return x * 2

fn main():
    val calc = Calculator {}
    var res = 0
    context calc:
        res = double(21)
    print(res)

main()
```

`bin/release/x86_64-unknown-linux-gnu/simple run <this file>` → prints `42`
(correct: `double(21) == 42`, and the write to outer `res` is visible).

The identical body inside an `it` block in
`test/feature/usage/classes_spec.spl` (`it "dispatches method to context
object"`) fails under
`SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/classes_spec.spl --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g'`
with `expected 0 to equal 42` — same for `self`-field access inside a
context method (`accesses self fields in context method`) and
`method_missing` dispatch inside a context block (`uses method_missing in
context block`).

## Root-cause hypothesis

Not traced into the Rust SSpec-evaluator source (out of scope for a
spec-triage pass; needs a rebuild to verify any fix). Candidate: the
`context <obj>: <body>` desugaring runs the body in a scope that correctly
threads back to the enclosing function scope under the top-level
interpreter (`run`) but is isolated (writes don't propagate back) under the
per-`it`-block scope wrapper the SSpec runner uses — plausibly the same
scope-chain-threading gap as the `while val` binding-visibility bug filed
alongside this one. Needs Rust-side scope-chain tracing across both
constructs to confirm whether they share one root fix.

## Notes

- Do NOT attempt a Rust seed source fix here (out of scope for a
  spec-triage pass; needs a rebuild to verify).
- No spec assertions were weakened — `expect res == 42` is unchanged in all
  three `it` blocks; they remain correctly RED against the real defect.
- The spec file itself documents this general area as fragile: line 174-175
  comment reads "# are skipped but verified via Rust tests in
  interpreter_oop.rs" for the group directly preceding these three tests,
  suggesting `context`-block semantics have known interpreter-vs-runner
  gaps already tracked informally.

## Affected specs (cluster `feature/usage`, 2026-07-20 triage)

- test/feature/usage/classes_spec.spl (3 of 23 examples: `dispatches method
  to context object`, `accesses self fields in context method`, `uses
  method_missing in context block`; all others green)
- test/feature/usage/structs_spec.spl (2 of 10 examples: `dispatches
  methods to context object`, `accesses self fields in context`; same
  `expected 0 to equal 42` shape, same `context <obj>:` construct, this
  time wrapping a `struct` instead of a `class`)

Verified with:
`SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/classes_spec.spl --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g'`
→ `Passed: 20, Failed: 3`
`SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/structs_spec.spl --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g'`
→ `Passed: 8, Failed: 2`
