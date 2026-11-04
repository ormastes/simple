# Seed: `i32` arithmetic overflow diverges between interpreter and JIT

- **Status:** OPEN — recorded 2026-11-05, measured, NOT fixed (record-only per
  the review of the `work/seed-i32-width-20261104` lane).
- **Engines:** Rust seed (`src/compiler_rust`), `SIMPLE_EXECUTION_MODE=interpreter`
  vs `SIMPLE_EXECUTION_MODE=jit`. Binary: `cargo-rel100/release/simple`
  built from `work/seed-i32-width-20261104` (declared-width dispatch table
  only; this divergence predates that lane — the interpreter has never
  carried a signed width on `Value::Int`).
- **Related:** `doc/08_tracking/bug/primitive_receiver_trait_impl_dispatch_2026-08-07.md`
  (the dispatch fix deliberately keeps `Value::Int` width-less; this record is
  the arithmetic half of the same gap).

## Measured

```
fn main():
    val m: i32 = 2147483647
    val n = m + 1
    print("i32_max_plus_1 " + n.to_text())
    val k: i32 = -2147483648
    print("i32_min_minus_1 " + (k - 1).to_text())
```

| expression | interpreter | JIT (cranelift) |
|---|---|---|
| `i32::MAX + 1` | `2147483648` (promotes to i64) | `-2147483648` (wraps at 32 bits) |
| `i32::MIN - 1` | `-2147483649` | `-2147483649` (does NOT wrap — the JIT itself is inconsistent between the two edges) |

## Why

- Interpreter: `val m: i32` binds a plain `Value::Int(i64)`; the declared width
  is not applied to arithmetic (only unsigned widths are, via
  `Value::UInt { width }` and `coerce_to_declared_unsigned`,
  `interpreter/node_exec.rs`). So every signed sub-i64 op is i64 arithmetic.
- JIT: `i32` locals are lowered as 32-bit values for `+` (wrap), but the `- 1`
  path on the `i32::MIN` operand evidently went through a 64-bit op, so the
  JIT wraps on one edge and not the other.

## Expected (pure-Simple contract)

The pure-Simple compiler types `m + 1` as `i32` (literal adopts the typed
operand), so native code wraps on BOTH edges. Whichever semantics the language
spec fixes for signed overflow (wrap vs trap), the three engines must agree;
today none of the three agree with each other on `i32::MIN - 1` vs
`i32::MAX + 1`.

## Not fixed because

Applying the declared width to signed arithmetic in the interpreter means a
width-carrying signed value or a declared-type coercion at every arithmetic
site — the design the dispatch lane rejected for blast radius (~4,300
`Value::Int` match sites, ~16,700 `i8/i16/i32` bindings in `src/lib`). It
needs its own lane with a spec pinning both edges in all three engines first.

## Repro

```
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <file above>
SIMPLE_EXECUTION_MODE=jit         bin/simple run <file above>
```
