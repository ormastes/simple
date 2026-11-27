# Bug: `unwrap else:` fallback closure side effects not visible to enclosing scope (seed interpreter)

- **Date:** 2026-11-25
- **Status:** open
- **Severity:** Medium (wrong answer, no diagnostic — closure runs but its
  mutations are lost, or the closure is skipped; only observed under the seed
  interpreter)
- **Area:** `src/compiler_rust/compiler/src/interpreter/expr.rs`
  (`Expr::UnwrapElse` arm, `call_closure_no_args`), deployed tracked seed
  `bin/simple.exe` (v1.0.0-rc.1)
- **Found while:** verifying
  `doc/08_tracking/bug/unwrap_or_return_default_value_dropped_2026-07-20.md`
  (that bug is fixed; these failures are in the sibling `unwrap else:`
  context of the same spec)

## Symptom

`test/feature/usage/safe_unwrap_operators_spec.spl`, context "unwrap else:
with lazy evaluation", 3 of 6 examples fail at release/1.0.0 HEAD
(`f3fb8f24dc9`):

```
✗ calls closure only when Option is None      expected false to equal true
✗ evaluates closure for Result Err            expected false to equal true
✗ closure can perform side effects            expected 0 to equal 100
```

The passing siblings ("returns value when Option is Some without calling
closure", "works with Result Ok without evaluating closure", "lazy evaluation
skips expensive computation when value exists") only assert that the closure
is NOT called on the present path. Every failing case asserts an effect of
CALLING the closure on the absent path (a flag set, a counter mutated). The
uniform pattern — present-path skips pass, absent-path effects are invisible —
points at the fallback closure's captured-variable mutations not propagating
back to the enclosing environment under the tree-walking interpreter
(`call_closure_no_args`), not at the `UnwrapElse` dispatch itself.

## Reproduce

```
SIMPLE_LIB=src bin/simple.exe run test/feature/usage/safe_unwrap_operators_spec.spl --mode=interpreter
=> 23 examples, 3 failures (the three above)
```

Windows worktree, tracked seed `bin/simple.exe` (38,403,072 bytes). The
`test` subcommand is unusable at HEAD (pinned seed rejects
`@representation_boundary`, carried by the test runner itself), so the `run`
harness was used; same evaluator.

## Not yet isolated

Whether the closure body executes at all on the absent path (dispatch bug)
or executes with a copied environment whose writes are discarded
(capture-semantics bug). The interpreter arm at
`src/compiler_rust/compiler/src/interpreter/expr.rs:540-555` evaluates the
fallback via `call_closure_no_args` when `try_unwrap_option_or_result`
returns `None`; start by probing whether a `print` inside the fallback fires.
Not checked against the pure-Simple self-hosted compiler or the JIT path.
