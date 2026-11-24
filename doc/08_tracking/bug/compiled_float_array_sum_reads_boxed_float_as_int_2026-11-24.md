# Compiled `[f64].sum()` returns a pointer-sized integer, not the float sum

- **Filed:** 2026-11-24
- **Status:** open
- **Area:** Rust seed HIR/MIR lowering of `arr.sum()` (JIT `simple run` and native-build)
- **Found by:** compiler-numeric-conv lane (work/compiler-numeric-conv-20261124), while fixing
  `interp_unsigned_array_sum_returns_zero_2026-11-23.md`

## Repro

```simple
fn main():
    val af: [f64] = [1.5, 2.25]
    val mixed = [1, 2.5]
    print("f64 sum {af.sum()}")
    print("mixed sum {mixed.sum()}")
```

Measured 2026-11-24 on aarch64, seed built from release/1.0.0 `91681a19c8c` plus the
unsigned-sum fix:

| row | interpreter | JIT (`run`) | native-build |
|---|---|---|---|
| `[1.5, 2.25].sum()` | 3.75 | 6568515026673 | 429872289 |
| `[1, 2.5].sum()` | 3.5 | 6568515026545 | 429884961 |

The compiled values change run to run: they are heap addresses.

## Cause (located, not fixed)

`rt_array_sum` (Rust `runtime/src/value/collections.rs`, C `runtime_native.c`) returns a
boxed FLOAT when any element is a float. HIR types `sum` as `I64` for every receiver
(`hir/lower/expr/mod.rs`, the `"sum" => Some(TypeId::I64)` row) and the MIR lowering
(`mir/lower/lowering_expr_method.rs`, `method == "sum"`) unboxes the result with
`unbox_dict_read_result(raw, TypeId::I64)`, so the boxed float handle is read as an int.

## Fix direction

Type `sum` by the element type (f64/f32 arrays -> F64, int/unsigned -> I64) in HIR, and
unbox with that type in MIR. Mixed/untyped arrays need the runtime tag (unbox as ANY).
Integer arrays are already correct on every engine.
