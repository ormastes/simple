# Unsafe capability block cannot initialize a value
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** open parser/lowering bug, source and execution reproduced

The Rust bootstrap parser accepts lexical capability blocks as statements:

```simple
var value: i64 = -1
unsafe(capabilities: [ffi]):
    value = rt_clock()
```

It rejects the equivalent compact block expression:

```simple
val value = unsafe(capabilities: [ffi]):
    rt_clock()
```

`bin/simple check` reports `unexpected token in expression: ':'` at the block
colon, followed by an unexpected indent. This prevents a safe, compact
proof-producing lift at SFFI boundaries and forces a mutable staging local.

The `rt_time` hardening uses the accepted statement form so safety work can
continue. Fix the parser and HIR lowering so an unsafe block is a normal block
expression whose value is its tail expression; retain the same lexical
capability metadata and erase it only after safety checking.


---

## Triage 2026-11-13 (lane p3-misc-b) — seed parser lane; not chaseable here

Fix surface is the Rust seed parser/HIR (`bin/simple check` rejecting
`val x = unsafe(...): ...` with `unexpected token in expression: ':'`).
This lane runs the prebuilt seed only (no cargo/rustc), so the parser cannot
be repaired or re-verified here. The accepted statement-form workaround in
`rt_time` hardening remains valid. Recorded for the seed parser lane.


---
## 2026-11-13 triage — lane live-p3-l6 (Windows host, seed bin/simple.exe, base f790f7f266e)

Verified FIXED at tip. The compact block-expression form
(`val value = unsafe(capabilities: [ffi]): <tail>`) is accepted and the pinning
specs all pass on the seed: `unsafe_call_argument_parser_spec` 8/8,
`unsafe_block_expression_spec` 5/5, `unsafe_block_binding_type_spec` 3/3. The
comp9 lane's 2026-11-11 expression-position parser fix covers this record's
exact repro shape. No in-lane change.
