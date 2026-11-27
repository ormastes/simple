# Compiled `[f64].sum()` returns a pointer-sized integer, not the float sum

- **Filed:** 2026-11-24
- **Status:** fixed 2026-11-24 for typed `[f64]`/`[f32]` receivers (work/compiler-numeric-conv2-20261124); untyped mixed arrays still open
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

## Cause

`rt_array_sum` (Rust `runtime/src/value/collections.rs`, C `runtime_native.c`) returns a
boxed FLOAT when any element is a float. HIR types `sum` as `I64` for every receiver
(`hir/lower/expr/mod.rs`, the `"sum" => Some(TypeId::I64)` row) and the MIR lowering
(`mir/lower/lowering_expr_method.rs`, `method == "sum"`) unboxes the result with
`unbox_dict_read_result(raw, TypeId::I64)`, so the boxed float handle is read as an int.

## Fix direction

Type `sum` by the element type (f64/f32 arrays -> F64, int/unsigned -> I64) in HIR, and
unbox with that type in MIR. Mixed/untyped arrays need the runtime tag (unbox as ANY).
Integer arrays are already correct on every engine.

## Resolution (2026-11-24)

**Fix.** HIR (`hir/lower/expr/mod.rs`, row `"sum"`) types `sum` as `F64` when the receiver
is `[f64]` or `[f32]`. MIR (`lowering_expr_method.rs`) reads the same element type from the
type registry and unboxes `rt_array_sum`'s result as `F64` instead of `I64`. Every other
receiver keeps `I64`, so int and unsigned sums are unchanged.

**Evidence.** `src/compiler_rust/compiler/tests/float_array_sum_engine_parity.rs` has 9 rows:
`[f64]`, negatives, `[f32]`, one element, 1e20, the sum bound to a typed local, the sum
returned from a `-> f64` fn, plus int and u32 controls.

| seed | interpreter | JIT |
|---|---|---|
| base (`4a32e48fb62`, the numconv tip) | pass | FAIL at row 1 |
| head | pass | pass |

Probe on head (interpreter / JIT / native-build, all identical):
- `[1.5, 2.25].sum()` = 3.75
- `[1.5f32, 2.25f32].sum()` = 3.75
- min/max of `[f64]`, `[u8]`, `[i64]`, `[u64]` all agree.

**Still open.**
- An untyped mixed array (`[1, 2.5]`, element type not F32/F64) still unboxes as `I64`.
  Typing the result `ANY` would send every int sum on an untyped array through dynamic
  dispatch, so it was left alone.
- An empty `[f64]` prints `0` in the interpreter and `0.0` compiled. The values compare
  equal; the interpreter cannot see the element type of an empty array.

**Same lane: `rt_array_min` C twin.** The C runtime (`runtime_native.c`) now defines
`rt_array_min`, mirroring the C `rt_array_max` and the Rust lane: nil for an empty array or
a non-array, and raw unsigned compare for packed `[u8]`/`[u64]`. Before this,
native-build of any `[T].min()` program failed to link.
- Selfcheck: `src/runtime/test/rt_array_min_selfcheck.c`, 24 checks. Base: link error
  `undefined symbol: rt_array_min`. Head: PASS.
- The `rt_array_min rust-only` row is removed from
  `scripts/check/rt_dual_implementation_baseline.txt`, since the symbol is now dual.
- It is pinned in the core-C symbol test in `pipeline/native_project/tests.rs`.
