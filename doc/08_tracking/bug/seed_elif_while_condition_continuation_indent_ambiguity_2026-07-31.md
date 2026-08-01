# Seed `elif`/`while` Condition Continuation vs. Block-Indent Ambiguity

## Status

**CLOSED 2026-08-01.** Fixed in source by `parse_condition_block`; see
`elif_condition_deep_continuation_indent_ambiguity_is_now_supported` in
`src/compiler_rust/parser/src/expressions/binary.rs`.

Re-measured 2026-08-01 with `cargo test -p simple-parser` against the TIP
crate: a 27-cell sweep (`if` and `elif`, operators `==` and `or`, continuation
columns 5..13 with the header at col 4 and the block body at col 8) is
**PARSE_OK in every cell**. The originally reported boundary — "cols 5-8 parse,
cols 9-13 do not" — no longer reproduces at tip.

Why the report outlived the fix: the boundary was measured against the
**deployed `bin/simple_seed`**, a 2026-07-25 build that predates
`parse_condition_block`. Probing with that binary reproduces already-fixed
parser bugs verbatim, indistinguishable from open gaps. Always re-measure a
seed parser claim with `cargo test -p simple-parser` at tip.

Downstream correction: `scripts/check/check-seed-parse-superset.shs` carried
this boundary as "RULE B" and was therefore **rejecting legal code**. RULE B
has been deleted and its two fixtures re-pinned as must-NOT-flag negatives so
it cannot be reintroduced. See
`parser_leading_operator_line_continuation_2026-08-01.md`.

The original analysis below is retained for the record; it describes the
mechanism that `parse_condition_block` now handles.

## Reproduction

A multi-line condition's trailing-operator continuation
(`skip_newlines_and_indents_for_method_chain`) consumes an INDENT token for
the continuation line whenever that line is indented deeper than the
condition's own line. The matching DEDENT for that pseudo-level does not
appear until the lexer's indentation stack next pops past it — and where that
lands in the token stream depends on whether the continuation line's column is
**deeper** or **shallower** than the following block body's column:

- Deep (continuation column > body column): the compensating DEDENT appears
  immediately after the condition's `Newline`, before the block's own
  `Indent`.
- Shallow (continuation column < body column): the compensating DEDENT does
  not appear until after the whole block body, alongside the block's own
  terminating DEDENT.

`parse_if`'s primary block-style path (`control_flow.rs`, save/reset
`deferred_dedent_count` around `parse_block()`, drain after) only handles the
**shallow** case. `parse_while`'s block-style path (drain `deferred_dedent_count`
between the condition's `Newline` and the block's `Indent`) only handles the
**deep** case. Neither handles both, and the elif-specific fix landed
alongside this doc (which reuses `if`'s drain-after strategy) inherits the
same shallow-only coverage.

Confirmed via the Rust seed unit tests (`comparison_continuation_tests`
module):

- `if a >\n         b:\n        return 2` (deep) — `UnexpectedToken { expected:
  "expression", found: "Indent" }`. Same failure shape for the primary `if`
  (not just `elif`), proving this is not elif-specific.
- `while a >\n       b:\n        i = i + 1` (shallow) — `UnexpectedToken {
  expected: "expression", found: "Dedent" }`, despite `while`'s existing
  passing test (`while_condition_comparison_continuation_parses`) using the
  deep shape.

## Pure-Simple engine

Not reproducible. The self-hosted pure-Simple parser
(`src/compiler/10.frontend/core/parser_stmts.spl`) has no analogous
`deferred_dedent_count`/pseudo-indent bookkeeping at all, and both the deep
and shallow shapes (for `if`, `elif`, and control-flow condition
continuation generally) parse past `parse_module_body` cleanly when compiled
with a self-hosted stage3 binary (`build/native_probe/stage3-explicit/simple
compile --format=smf`) — consistent with the established pattern that this
class of continuation defect lives only in the legacy Rust seed's hand-rolled
layout-token handling, not the pure-Simple grammar.

## Fix (not done here)

Needs a single reconciliation strategy that is correct regardless of whether
the continuation pseudo-level sits above or below the following block's own
level — e.g. tracking pseudo-indent levels on an explicit stack rather than a
flat `deferred_dedent_count`, or having the lexer suppress INDENT/DEDENT
emission entirely while a binary expression continuation is open. Either is a
statement/expression boundary change and should be scoped as its own task.
