# A float flowing into an int-typed parameter or return: engines disagree

- **Filed:** 2026-11-24
- **Status:** open. Needs an owner decision: reject it in the type checker, or coerce it
  everywhere.
- **Area:** Rust seed type checking, interpreter call/return, and Cranelift uniform i64 ABI
- **Found by:** compiler-numeric-conv2 lane (work/compiler-numeric-conv2-20261124), while
  routing the narrow-slot adapters through `float_to_int_saturating`

## Repro

```simple
fn r32(x: f64) -> i32:
    x
fn take8(v: u8) -> i64:
    v as i64
fn main():
    print("r32 2.5 {r32(2.5)}")
    print("take8 300.5 {take8(300.5)}")
```

Measured 2026-11-24 on aarch64, seed at numconv tip `4a32e48fb62`:

| row | interpreter | JIT |
|---|---|---|
| `r32(2.5)` (float returned from `-> i32`) | `2.5` (no coercion) | `4612811918334230528` (f64 bits) |
| `r32(1e20)` | `100000000000000000000.0` | f64 bits |
| `take8(300.5)` (float passed to `u8`) | `300` (truncated, not narrowed) | `0` |

The program is accepted without any diagnostic. None of the three engines agrees with an
explicit `as` cast (which saturates: 2, 255).

## Cause

The type checker accepts a float where an int-typed parameter or return is declared, but no
engine inserts a conversion:
- The interpreter keeps the float in an int-typed return, and truncates without narrowing
  for an argument.
- The JIT moves values through the uniform i64 slot. A float return keeps its bits (see
  `body.rs` Return lowering). A float argument reaches the callee's int vreg as bits, then
  narrows.

The narrow-slot adapters in `adapt_value_to_type` / `calls.rs` / `body.rs`, now
saturating, only fire for Cranelift-typed narrow slots (runtime/SFFI signatures), not for
these user functions.

## Fix direction

Either reject an implicit float -> int at the call/return site (the user writes `as T`, which
saturates on every engine), or have HIR insert the same saturating cast. Owner decision.
