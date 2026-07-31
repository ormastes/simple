# Seed `elif`/`while` Condition Continuation vs. Block-Indent Ambiguity

## Status

OPEN, SEED-ONLY. Not a regression from the `elif`-specific fix landed the same
day (see `elif_condition_continuation_is_still_unsupported` in
`src/compiler_rust/parser/src/expressions/binary.rs`); it is a pre-existing,
orthogonal gap in the Rust seed's layout-token bookkeeping that this task
explicitly scoped out (touching it means changing how INDENT/DEDENT interact
with expression parsing — a statement/expression boundary change, not a
contained patch).

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
