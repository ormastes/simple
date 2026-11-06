# Seed: `i32` arithmetic overflow diverges between interpreter and JIT

- **Status:** fixed. Interpreter fixed 2026-11-06 (branch
  `work/seed-interp-correctness-20261106`), see "Resolution". JIT/codegen half fixed
  2026-11-06 (branch `work/seed-jit-batch2-20261106`), see "Resolution (JIT)".
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

## Resolution (2026-11-06, interpreter half)

Instead of a width-carrying signed value, the interpreter now applies the
STATIC width the pure-Simple checker assigns, using the per-frame declared
widths the dispatch lane already records (`Env::declared_int_width`):

- `interpreter/expr/ops.rs` `static_int_width`: identifier with a declared
  i8/i16/i32 width, `as iN` cast, `iN`-suffixed literal, unary `-`/`~`, and
  `+ - * / % & | ^` (an unsuffixed literal adopts the typed operand;
  mismatched or unknown widths stay i64; shifts take the left operand's
  width). The Int fast path wraps its result to that width
  (`wrap_signed`, two's complement) — only checked when the result is outside
  i8, so the hot small-int path does no extra work.
- `interpreter/node_exec.rs` `exec_augmented_assignment`: `x op= rhs` wraps to
  `x`'s declared width (the RHS temp hid it from the binary-op wrap).
- `record_let_declared_width`: an unannotated `val n = m + 1` inherits the
  initializer's static narrow width, so later arithmetic on `n` wraps too.
  An annotated binding now takes its width from the annotation only.

Not changed: binding a declared `i32` from an out-of-range value
(`val x: i32 = 3000000000`) still stores the i64; only arithmetic wraps.

Evidence (`test/fixtures/seed_interp/i32_overflow_repro.spl`, interpreter):

| expression | before (seed 2026-10-05) | after (this branch) |
|---|---|---|
| `i32::MAX + 1` | `2147483648` | `-2147483648` |
| `i32::MIN - 1` | `-2147483649` | `2147483647` |

JIT on the same build still prints `-2147483648` / `-2147483649` (its
`MIN - 1` edge does not wrap) — that is the codegen half, owned separately.

Rust tests in `interpreter/expr/ops.rs`: `i32_declared_arithmetic_wraps_on_both_edges`
(before: `left: 8, right: 127`; after ok), `i32_param_arithmetic_wraps`
(before `0` vs `1`; after ok), `untyped_and_i64_arithmetic_still_promotes`
(ok before and after — guards the i64 path).

## Resolution (JIT)

Root cause: `codegen/instr/core.rs::compile_binop` computes every integer op in
i64. A narrow result was only wrapped by an incidental narrowing `Store` into a
typed local. `val n = m + 1` therefore wrapped, while `(k - 1)` used directly as
an operand did not. MIR for the repro showed `Store ty=i32` after the `Add` and
no narrowing after the `Sub`.

Fix: `compile_binop` now narrows `+ - * / <<` results to the declared width
(`ireduce` then `sextend` or `uextend`) through `narrow_arith_width`. That function
mirrors the interpreter's `static_int_width` rule: both operands share one narrow
width, or one is narrow and the other is an untyped literal (`iconst`). For
`u8`/`u16`/`u32` the literal must also fit the width, as in
`uint_arith_wrap_width`. An i64 variable operand keeps the result wide on both
engines.

Fixture `test/fixtures/compiler/seed_jit_miscompiles/i32_min_minus_one_wrap.spl`:

| engine | before (base ecb705896a4) | after |
|---|---|---|
| JIT | `i32_min_minus_1 -2147483649`, `rev 2147483649 u -1 s -32769 b 256` | `2147483647`, `rev -2147483647 u 4294967295 s 32767 b 0` |
| interpreter | `2147483647`, `rev -2147483647 u 4294967295 s 32767 b 0` | unchanged |

Rust test `compiler/tests/i32_overflow_wrap_jit.rs`:
`i32_arithmetic_wraps_on_both_edges_without_a_narrowing_store` (before: FAILED
`left: 2`; after ok), `narrow_unsigned_and_i16_arithmetic_wraps` (before:
FAILED `left: 1`; after ok).

Known limit: a literal defined in another MIR block reaches codegen through a
Cranelift variable rather than an `iconst`, so it is treated as a wide
operand and the result is not narrowed. That is the old behaviour, not a new
divergence.
