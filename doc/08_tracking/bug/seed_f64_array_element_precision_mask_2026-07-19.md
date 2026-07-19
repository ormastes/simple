# `[f64]` array element read-back loses precision (tagged-float mask on rt_array_get)

- **id:** seed_f64_array_element_precision_mask_2026-07-19
- **status:** open
- **severity:** high (silent miscompile — arrays of floats are ubiquitous)
- **class:** tag-box `<<3`/`>>3` mask — the **array-element sibling** of the
  enum-payload f64 mask fixed in `fc7cdcb0b90`
  (`doc/08_tracking/bug/native_llvm_f64_enum_payload_argpass_2026-07-19.md` is
  the native-backend cousin).
- **found on:** the deployed `bin/simple`
  (`bin/release/x86_64-unknown-linux-gnu/simple`), which is currently the **Rust
  bootstrap seed** (prints the "bootstrap seed only" banner) — i.e. today's
  shipping tool.

## Symptom

An `f64` read back out of an array is corrupted: any value with nonzero low
mantissa bits (e.g. `0.1`) reads back slightly wrong, so `arr[0] == 0.1` is
false. Confirmed for both an untyped literal and a **typed `[f64]` parameter**.
Scalar `f64` values (params, locals) are correct — the loss is specific to array
element extraction.

Repro (typed `[f64]` param), deployed seed → **rc=40** (expected 30):

```simple
fn first(xs: [f64]) -> f64:
    return xs[0]

fn main() -> i64:
    val a = [0.1, 0.2, 0.3]
    val x = first(a)
    if x == 0.1:
        return 30
    return 40
```

Control (scalar f64) → rc=30 (correct):

```simple
fn ident(v: f64) -> f64:
    return v
fn main() -> i64:
    if ident(0.1) == 0.1: return 30
    return 40
```

## Root cause (same class)

`rt_array_get` returns a TAGGED runtime value (`value << 3` for small values;
see `src/compiler/50.mir/mir_lowering_stmts.spl:1713`). For an `f64` element the
extract applies the tagged-float mask `(bits >> 3) << 3`, zeroing the low 3
mantissa bits — exactly the leak fixed for enum payloads in `rt_enum_payload`
(`src/compiler_rust/.../mir/lower/lowering_expr_builtin.rs`, commit fc7cdcb0b90).
The array path is disjoint from the enum path (that fix is gated on
`name == "rt_enum_payload"`), so the enum fix does **not** cover this.

## Fix sketch

At the array-element extract, when the element type is F64, reinterpret the raw
i64 bits (`Cast{F64→F64}` / bitcast) instead of applying the tagged-float mask —
the same shape as the enum-payload fix. Locate the seed's array-element float
unbox (the `rt_array_get` result coercion). Needs a seed rebuild to verify
(disk-gated).

## Scope note

Confirmed on the deployed seed. The pure-Simple self-hosted MIR lowering has no
`UnboxFloat` instruction (uses `emit_bitcast`/`emit_cast`); its `rt_array_get`
f64 behavior was not run here (the self-hosted binary is not currently deployed —
the "redeploy wall"). Re-run this repro through the self-hosted `bin/simple`
once it is built to confirm whether pure-Simple is already clean.

## Regression guard

Add a `[f64]` element precision case (assert `[0.1][0] == 0.1`) once fixed —
mirror `test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl`.
