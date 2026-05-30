# Generic BTree Spike Parse Failure — FULLY RESOLVED

## Status

**Rust seed parser:** Fixed. `try_skip_ident_generic_args` in
`src/compiler_rust/parser/src/expressions/postfix.rs` (lines 1085–1187)
commits on `Dot` after `>`. Tests run through the seed: 8/8 passing.

**Self-hosted `.spl` parser:** Fixed (2026-05-29). `parse_postfix()` and
`parse_postfix_on()` in `src/compiler/10.frontend/core/parser_expr.spl` both
call `try_skip_ident_generic_args()` after parsing a bare `EXPR_IDENT` primary
when the current token is `TOK_LT` (82) or `TOK_LT_GENERIC` (86). The
speculative-skip function uses `lex_snapshot_save`/`lex_snapshot_restore` and
`parser_tok_save`/`parser_tok_restore` for complete state save/restore, matching
the Rust seed's logic exactly. The self-hosted binary is at `v1.0.0-beta` and
no longer segfaults. The prior "open gap" and "segfault-blocked verification"
notes no longer apply.

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

## .spl Parser Fix (implemented)

`try_skip_ident_generic_args()` in `src/compiler/10.frontend/core/parser_expr.spl`
(lines ~533–615) implements the speculative-skip logic:

1. Saves full lexer + token state via `lex_snapshot_save()` + `parser_tok_save()`
2. Depth-tracking loop over `<...>` consuming idents, commas, and type-expression
   punctuation; handles nested `<` and `>>` (depth==2 case)
3. Commits (leaves parser positioned after `>`) only when `DOT`(164), `LPAREN`(140),
   or `COLON_COLON`(162) follows `>`
4. Backtracks via `lex_snapshot_restore()` + `parser_tok_restore()` otherwise,
   leaving `<` for the binary-expression layer (less-than comparison)

Called at both `parse_postfix()` (line ~752) and `parse_postfix_on()` (line ~621)
after an `EXPR_IDENT` primary is parsed and the next token is `TOK_LT`/`TOK_LT_GENERIC`.

## Coverage

All forms covered by `test/feature/language/generic_btree_spike_spec.spl`:
- `TestNode<i64>.new()` — single-param generic static call
- `TestNode<text>.new()` / `.insert(...)` — generic with text type param
- `BTreeNode<i64, text>.new(k, v)` — two-param generic static call
- `SortedNode<i64>.new()` — generic with where clause
- Type alias static constructors (`IntNode.new()`, `TextNode.new()`)
