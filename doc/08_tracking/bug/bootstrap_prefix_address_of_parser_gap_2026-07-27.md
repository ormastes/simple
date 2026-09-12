# Bootstrap Parser Rejects Prefix Address-Of Expressions

- **Date:** 2026-07-27
- **Area:** pure-Simple parser / unary expressions
- **Severity:** high — blocks the strict Stage 4 full-CLI bootstrap.
- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
