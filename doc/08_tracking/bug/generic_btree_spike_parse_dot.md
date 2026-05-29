# Generic BTree Spike Parse Failure — RESOLVED

## Status

Fixed (2026-05-29). Two complementary fixes:

1. **Rust seed parser** (`src/compiler_rust/parser/src/expressions/postfix.rs`):
   Already had `try_skip_ident_generic_args` which commits on `Dot` after `>`.
   Tests run through the seed (8/8 passing).

2. **Self-hosted `.spl` parser** (`src/compiler/10.frontend/core/parser_expr.spl`):
   Added matching speculative skip logic so bootstrap can parse this syntax.
   Also exports added to `parser.spl` and `__init__.spl`.

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
The `.spl` parser would have emitted `unexpected token in expression: '.'`.

## Root Cause

`parse_postfix()` (both Rust seed and `.spl` parser) previously returned from
the primary parse with `Identifier("Foo")` as the base expression, then saw
`<` and left it for the binary-expression layer to handle as a less-than
comparison. This consumed `i64`, then `>`, leaving `.new()` as the next tokens —
which the expression layer couldn't start with `Dot`.

## Resolution

**Rust seed** (`src/compiler_rust/parser/src/expressions/postfix.rs`, lines 140–157):
`try_skip_ident_generic_args()` speculatively consumes `<TypeArgs>` and commits
only when `Dot`, `LParen`, or `DoubleColon` follows. Already fixed before 2026-05-29.

**`.spl` parser** (new, 2026-05-29):
Added equivalent speculative skip block in `parse_postfix()` in
`src/compiler/10.frontend/core/parser_expr.spl` immediately after
`var base = parse_primary_expr()`. Saves lexer and parser token state,
consumes `<...>` tracking nesting depth, commits on Dot/LParen/DoubleColon
after `>`, backtracks on failure.

Supporting changes:
- `src/compiler/10.frontend/core/parser.spl`: exported `par_kind_set`,
  `par_text_set`, `par_line_set`, `par_col_set`
- `src/compiler/10.frontend/core/__init__.spl`: re-exported those setters
- `src/compiler/10.frontend/core/parser_expr.spl`: added imports for
  `TOK_COLON_COLON`, lexer state functions, and parser state setters

## Coverage

All forms covered by `test/feature/language/generic_btree_spike_spec.spl`:
- `TestNode<i64>.new()` — single-param generic static call
- `TestNode<text>.new()` / `.insert(...)` — generic with text type param
- `BTreeNode<i64, text>.new(k, v)` — two-param generic static call
- `SortedNode<i64>.new()` — generic with where clause
- Type alias static constructors (`IntNode.new()`, `TextNode.new()`)
