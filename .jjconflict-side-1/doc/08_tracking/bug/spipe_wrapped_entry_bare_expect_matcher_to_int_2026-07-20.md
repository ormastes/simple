# Bare `expect X matcher(Y)` DSL breaks inside `fn main():` wrapper ("cannot convert matcher to int")

## Symptom

`test/01_unit/lib/editor/.spipe_wrapped_entry_split_pane_spec.spl` reports all 6
`it` blocks passing (`6 examples, 0 failures`), but the file-level test summary
still shows `Failed: 1` (`Files: 1, Passed: 6, Failed: 1`), caused by a trailing
error printed after all examples complete:

```
error: semantic: type mismatch: cannot convert matcher to int
error: test-runner: spec failed
```

## Root cause (isolated by diffing against an identical sibling spec)

This file is byte-for-byte the same test logic as
`test/01_unit/lib/editor/split_pane_spec.spl` (same `describe`/`it` bodies,
same bare `expect count to_equal(1)` DSL syntax — no `.` /parens around
`expect`), with exactly one structural difference: the `.spipe_wrapped_entry_`
variant wraps the whole `describe` block inside a top-level `fn main():`:

```spl
# .spipe_wrapped_entry_split_pane_spec.spl (FAILS with the trailing error)
fn main():
    describe "SplitPaneLayout":
        it "creates layout with single root pane":
            ...
            expect count to_equal(1)
```

```spl
# split_pane_spec.spl (PASSES cleanly, 6/6, 0 failures, no trailing error)
describe "SplitPaneLayout":
    it "creates layout with single root pane":
        ...
        expect count to_equal(1)
```

Confirmed via direct run of both:

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/editor/split_pane_spec.spl --no-session-daemon
# -> PASS, Passed: 6, Failed: 0

SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/editor/.spipe_wrapped_entry_split_pane_spec.spl --no-session-daemon
# -> FAIL, Passed: 6, Failed: 1 (all 6 examples individually pass; the file-level
#    failure comes solely from the trailing "cannot convert matcher to int" error)
```

The bare `expect X matcher(Y)` DSL form (desugared specially by the compiler,
since `expect` here takes no parens/dot) appears to be mis-lowered when the
`describe`/`it` tree is nested inside a function body rather than living at
module top level — something in that lowering path ends up trying to convert
the `matcher(Y)` desugar target to `int` in the `fn main():`-wrapped case only.

## Repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/01_unit/lib/editor/.spipe_wrapped_entry_split_pane_spec.spl --no-session-daemon
```

## Fix hypothesis (not attempted — compiler lowering issue, out of test-shard scope)

Whoever owns the bare-`expect`/matcher desugar pass (likely in the SSpec
front-end or the same layer that handles `describe`/`it` blocks) needs to check
why nesting the tree inside a `fn main():` body changes how the matcher
expression is typed/lowered. Since a functionally-identical non-wrapped sibling
spec passes cleanly, this is not a test-content bug — nothing in the `.spl`
file content is wrong, so no test-only edit can fix it.

## Affected specs

- `test/01_unit/lib/editor/.spipe_wrapped_entry_split_pane_spec.spl` (this is
  likely a broader pattern across all `.spipe_wrapped_entry_*` dotfiles in the
  suite that use the bare `expect X matcher(Y)` form inside `fn main():` — not
  independently verified against other `.spipe_wrapped_entry_*` files in this
  triage pass, flagging for whoever picks this up to check the wider
  `.spipe_wrapped_entry_*` family).
