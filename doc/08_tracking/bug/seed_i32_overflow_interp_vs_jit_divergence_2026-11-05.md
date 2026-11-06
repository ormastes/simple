# Seed: `i32` arithmetic overflow diverges between interpreter and JIT

- **Status:** FIXED in the interpreter 2026-11-06 (branch
  `work/seed-interp-correctness-20261106`) — see "Resolution" below. The JIT
  `i32::MIN - 1` edge (no wrap) remains a codegen-side gap, not fixed here.
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
