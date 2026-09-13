# Bug: Lean Parser Bitwise/Pipe Precedence Divergence

**Status:** OPEN (confirmed still reproduces 2026-09-12)

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

## Triage 2026-09-12
Re-verified 2026-09-12: still reproduces. `src/compiler/10.frontend/core/parser_expr.spl` has no `parse_bitwise_and/xor/or` functions and no `TOK_CARET` handling — the described precedence restructuring was never implemented; `parse_multiplication` remains the only level between comparison and unary. A runtime check via `bin/simple run` was inconclusive because that path exercises the Rust seed's own parser, not the lean self-hosted parser this record targets. Evidence: source grep above; seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
