# Bootstrap Parser Rejects Prefix Address-Of Expressions

- **Date:** 2026-07-27
- **Area:** pure-Simple parser / unary expressions
- **Severity:** high — blocks the strict Stage 4 full-CLI bootstrap.
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STALE-REF / UNDETERMINED

Same finding as bootstrap_parser_address_of_cast_2026-07-27: `address_of` does
not appear anywhere under `src/compiler/10.frontend/`, and the cited
`parser_types_expr.spl` has no address-of handling. Treat these two rows as ONE
root cause (prefix `&` parsing) and re-locate the parser site before any fix.
