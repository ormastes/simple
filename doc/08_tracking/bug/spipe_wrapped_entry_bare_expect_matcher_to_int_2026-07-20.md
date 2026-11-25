# Bare `expect X matcher(Y)` DSL breaks inside `fn main():` wrapper ("cannot convert matcher to int")
## Closed 2026-09-16 — ..._spec.spl --no-session-daemon ``` ## Fix hypothesis (not attempted — compiler lowering iss

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

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


## Verification 2026-11-25 (p2w5-ae lane)

Closure re-verified by source inspection at release/1.0.0 tip (4bc2c986375):

- The affected file
  `test/01_unit/lib/editor/.spipe_wrapped_entry_split_pane_spec.spl` no longer
  exists in the tree. None of the 7 surviving `.spipe_wrapped_entry_*`
  dotfiles uses the bare `expect X matcher(Y)` form, and dotfile specs are
  excluded from discovery (31a5bf2fec8, "dotfile exclusion").
- The wrapped-entry preprocessor rewrites bare infix `expect X matcher Y` to
  `expect(X).matcher(Y)` before the `fn main():` wrap:
  `src/app/test_runner_new/test_runner_execute.spl:233`
  (`spipe_rewrite_infix_expect_line`, applied at line 407), with pure-Simple
  mirrors in `src/lib/common/test_runner/native_framework_wrapper.spl:11` and
  `src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl:120`.
- The seed parser folds a matcher word after a parenthesized subject
  (5a3a5ce413f, `no_paren.rs`), pinned by
  `test/01_unit/app/test_runner_new/single_lane_paren_subject_matcher_word_spec.spl`;
  the bare paren-adjacent form (`expect count to_equal(1)`) remains common at
  module top level across the suite (e.g.
  `test/01_unit/lib/editor/multi_buffer_spec.spl`).

Verification limit: no live repro was possible on this host — the pinned Rust
seed rejects `@representation_boundary` at HEAD, so `bin/simple.exe test` is
non-functional repo-wide. Verification is by code inspection only.
Status remains Closed.
