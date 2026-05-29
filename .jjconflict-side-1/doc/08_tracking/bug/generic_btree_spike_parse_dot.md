# Generic BTree Spike Parse Failure — RESOLVED (seed) / OPEN (.spl gap)

## Status

**Rust seed parser:** Fixed. `try_skip_ident_generic_args` in
`src/compiler_rust/parser/src/expressions/postfix.rs` (lines 1085–1187)
commits on `Dot` after `>`. Tests run through the seed: 8/8 passing.

**Self-hosted `.spl` parser:** Gap remains open. `parse_postfix()` in
`src/compiler/10.frontend/core/parser_expr.spl` does NOT handle `<T>` before
`.method()`. The `.spl` parser is not currently exercised by the test runner
(seed interprets all tests; self-hosted binary segfaults due to unrelated
2026-05-27 interpreter issues). When bootstrap is restored, this gap will
need a verified speculative-skip fix mirroring the Rust seed's logic.

The fixture was promoted to active SPipe coverage:
- **Active test:** `test/feature/language/generic_btree_spike_spec.spl` (8 tests, all passing)
- **Fixture removed from:** `test/fixtures/repro/language/generic_btree_spike_spec.spl.fixture`

## Original Error

The former active spike spec at `test/spike/generic_btree_spike_spec.spl`
failed before execution:

```text
parse error: Unexpected token: expected expression, found Dot
```

The error message is from the Rust seed's `{:?}` Debug format (`found Dot`).
The `.spl` parser would emit `unexpected token in expression: '.'`.

## Root Cause

`parse_postfix()` (both Rust seed and `.spl` parser) parsed `Foo` as an
identifier primary, then saw `<` and left it for the binary-expression layer
as a less-than comparison. This consumed `i64`, then `>`, leaving `.new()` as
next — which the expression layer couldn't start with `Dot`.

## Rust Seed Fix (already applied)

`try_skip_ident_generic_args()` in `postfix.rs` (lines 1085–1187): after
parsing a primary `Identifier`, if next token is `Lt`, speculatively saves
full parser+lexer state, consumes `<...>` tracking nesting depth, and commits
only when `Dot`, `LParen`, or `DoubleColon` follows `>`. Otherwise backtracks.

The matching call is at `postfix.rs` lines 155–156:
```rust
if matches!(&expr, Expr::Identifier(_)) && self.check(&TokenKind::Lt) {
    self.try_skip_ident_generic_args();
}
```

## .spl Parser Gap (follow-up required)

When the self-hosted compiler is restored (after `bootstrap-from-scratch
--deploy` succeeds), the equivalent fix must be added to `parse_postfix()` in
`src/compiler/10.frontend/core/parser_expr.spl`. The implementation requires:

1. Speculative save/restore of `par_kind/par_text/par_line/par_col` + lexer
   `lex_pos/line/col` state — need to export `par_kind_set` etc. from
   `parser.spl` and `__init__.spl`
2. Depth-tracking loop over `<...>` consuming idents, commas, brackets
3. Commit only when `DOT`(164), `LPAREN`(140), or `COLON_COLON`(162) follows `>`
4. Verify: (a) `TestNode<i64>.new()` commits and works; (b) `i < 10` and
   `a < b` backtrack without corrupting parser state

Note: the backtrack path fires on every `identifier < expr` comparison in the
self-hosted compiler source, so the save/restore must be complete and correct.

## Coverage

All forms covered by `test/feature/language/generic_btree_spike_spec.spl`:
- `TestNode<i64>.new()` — single-param generic static call
- `TestNode<text>.new()` / `.insert(...)` — generic with text type param
- `BTreeNode<i64, text>.new(k, v)` — two-param generic static call
- `SortedNode<i64>.new()` — generic with where clause
- Type alias static constructors (`IntNode.new()`, `TextNode.new()`)
