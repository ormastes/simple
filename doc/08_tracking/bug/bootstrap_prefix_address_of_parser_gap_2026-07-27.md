# Bootstrap Parser Rejects Prefix Address-Of Expressions

- **Date:** 2026-07-27
- **Area:** pure-Simple parser / unary expressions
- **Severity:** high — blocks the strict Stage 4 full-CLI bootstrap.
- **Status:** RESOLVED 2026-11-25 (see resolution note at the end).

## Reproduction

```simple
var buf: [u64; 2] = [0, 0]
val address = &buf as u64
```

The Rust seed parser accepts `&` as `UnaryOp.Ref`, but the pure
`parse_unary()` handles `-`, `+`, `not`, and `~` only. It passes the leading
`&` to `parse_primary_expr()`, which reports `unexpected token in expression:
&`.

## Required Fix

Add prefix `&` and `&mut` parsing with the same precedence as the Rust parser,
map the flat unary token to `UnaryOp.Ref`/`RefMut`, and add a focused parser
and lowering regression. Until then, Stage 4 syscall sources use the existing
`unsafe_addr_of(value)` primitive.

## Evidence

The repaired strict bootstrap from checkpoint
`f461c1cb248150a116c05b95b42a0ba23b9a218c` first failed at
`src/os/userlib/device.spl:26` and exposed four more prefix-address uses in the
same file. A static scan found and normalized all 27 active uses in the
Stage 4 userlib source lane before the final bounded retry.

## Resolution 2026-11-25 (p2w1-ab lane, release/1.0.0 @ 38265c7f249)

Fixed as required. `src/compiler/10.frontend/core/parser_expr.spl:471`
`parse_unary()` now handles prefix `&` (`TOK_AMPERSAND`) and `&mut`
(`&` followed by ident `mut` maps to the negated op kind), matching the
flat-AST bridge at `_FlatAstBridge/convert_nodes.spl:670-671` which maps
kind 120 -> `UnaryOp.Ref` and -120 -> `UnaryOp.RefMut`. The focused
regression exists: `test/01_unit/compiler/frontend/flat_ast_address_of_spec.spl`
parses `&buf as u64`, `left & right`, and `&mut buf` through the flat-AST
path and checks the lowered MIR.

Verification limit: spec execution is blocked in this lane because the
pinned seed rejects the `@representation_boundary` decorator tree-wide
(cfd89933699); closure is by source inspection. Status: RESOLVED.
