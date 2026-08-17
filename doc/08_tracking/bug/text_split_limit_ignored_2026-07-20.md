# `text.split` limit ignored or mistyped

BugDB ID: `text-split-limit-ignored`
Priority: P2
Claimed: 2026-08-17, Codex `p2_text_split` lane

## Reproducer

`"a:b:c".split(":", 2)` must produce `["a", "b:c"]`. The same call with
the limit held in a variable must behave identically. Adjacent cases cover
limit one, a missing separator, an empty separator, and multibyte text and
delimiters in
`test/01_unit/compiler/interpreter/nested_string_split_spec.spl`.

No receipt-admitted Stage 4 test runner is available in the current worktree.
`bin/release/simple` is a wrapper around the known stale/status-139 deployed
runtime, so this continuation did not reclassify a source inspection or stale
execution as a reproducer PASS.

## Ownership and root cause

Both live Rust interpreter dispatchers already consume the second argument as
an integer and use bounded `splitn` semantics:

- `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`
- `src/compiler_rust/compiler/src/interpreter_method/string.rs`

The live pure-Simple interpreter likewise evaluates the second argument with
`val_get_int` in
`src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl`.

The remaining defect was the pure-Simple MIR native boundary. It selected
`rt_string_split_limit(value, separator, limit)` correctly, but passed every
method argument through `ensure_tagged_str`. That converted the numeric limit
to a string handle even though the runtime ABI requires raw `i64`.

## Fix

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` now tags the
separator but preserves split argument index one as its lowered numeric local.
All other text-special arguments retain their prior string tagging. No Rust or
foreign-runtime edit is required because delegation below the pure-Simple
boundary is already correct.

## Regression evidence

The focused SSpec retains the exact literal-limit reproducer and adds:

- a variable numeric limit, preventing another blanket string-tag regression;
- multibyte content with a multibyte separator, preserving the unsplit tail;
- limit one, missing separator, and empty-separator adjacency.

The live chained-call Rust dispatcher also has a direct unit contract for the
exact two-part result and Unicode empty-separator adjacency. The adjacent
macOS/Linux test-helper cfg defect was corrected, after which the focused
dispatcher contract executed successfully:

```sh
cargo test -q -p simple-compiler --lib string_split_honors_limit_and_unicode_empty_separator
# PASS: 1 passed
```

Source convergence is complete. Runtime closure remains pending one focused
interpreter and native run against a fresh receipt-admitted pure-Simple CLI:

```sh
SIMPLE_LIB=src <admitted-simple> test test/01_unit/compiler/interpreter/nested_string_split_spec.spl --mode=interpreter
SIMPLE_LIB=src <admitted-simple> test test/01_unit/compiler/interpreter/nested_string_split_spec.spl --mode=native
```

Do not mark the BugDB row fixed until both modes pass on that admitted binary.

## Knowledge update scope

- Text-split feature and interpreter-text-method layer expert notes now bind
  mixed-signature argument typing and cross-engine parity.
- `doc/07_guide/`: N/A; the public split contract is unchanged.
- Research/architecture/design: N/A; the existing MIR/runtime boundary remains
  authoritative.
- Workflow/SPipe/manual docs: N/A; no workflow or scenario-manual contract
  changed.
