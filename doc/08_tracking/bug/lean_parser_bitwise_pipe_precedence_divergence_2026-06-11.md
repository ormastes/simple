# Bug: Lean Parser Bitwise/Pipe Precedence Divergence
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Not closed 2026-09-13 — STILL REAL; fix blocked by a concurrent bootstrap

- **measured** `grep "fn parse_bitwise" src/compiler/10.frontend/core/parser_expr.spl` → no
  matches. The leveled chain is still `parse_multiplication` (line 413) → `parse_comparison`
  (line 292) with no bitwise levels in between.
- **measured** PIPE (kind 121) is still consumed at multiplication level:
  `parser_expr.spl:437` and `:524` both do `elif par_kind_get() == 121: ... expr_binary(121, ...)`.
- **measured** The Rust seed evaluates `12 & 10 + 1` as `8` (= `a & (b + c)`), i.e. the
  *intended* precedence, so the seed/lean divergence the entry describes persists.
- Left OPEN: the fix edits `src/compiler/10.frontend/core/parser_expr.spl`; a bootstrap is
  running concurrently in this workspace and a compiler-source edit would desync it.


**Date:** 2026-06-11
**Component:** src/compiler/10.frontend/core/parser_expr.spl

## Summary

The lean self-hosted parser handles `|` (PIPE, 121), `&` (AMPERSAND, 120), and `^` (CARET, 122)
at multiplication precedence level (same level as `*`, `/`, `%`, `**`).

`tokens.spl`'s `tok_precedence()` specifies the intended order as:
- pipe(4) < caret(5) < ampersand(6) < comparisons(7)

This means bitwise operators should be looser than comparisons, not tighter.

## Impact

Unparenthesized mixed expressions involving bitwise operators and arithmetic/comparison operators
may associate differently in the lean parser vs. the Rust seed compiler. Examples:

```
a & b + c      # lean: (a & b) + c   intended: a & (b + c)
a | b == c     # lean: (a | b) == c  intended: a | (b == c)
```

## Workaround

Parenthesize all mixed bitwise expressions until precedence levels are corrected:

```
(a & b) + c    # explicit — safe in both parsers
a | (b == c)   # explicit — safe in both parsers
```

## Fix Required

Introduce dedicated precedence levels for bitwise operators between multiplication and comparison
in the leveled chain: `parse_multiplication` → `parse_bitwise_and` → `parse_bitwise_xor` →
`parse_bitwise_or` → `parse_comparison`. This is a follow-up parser restructuring task.

## Related

- Lexer tokens: src/compiler/10.frontend/lexer_types.spl (kinds 120/121/122/123)
- tok_precedence (dead code, spec reference only): src/compiler/10.frontend/core/tokens.spl
- M1 parser fix commit: landed infix &/^ + prefix ~ at multiplication level as deliberate
  short-term placement matching existing PIPE placement (1ea5249607 + follow-up fix commit).

