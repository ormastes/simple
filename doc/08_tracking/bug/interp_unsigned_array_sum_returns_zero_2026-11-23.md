# Interpreter: `[u32].sum()` returns 0 (unsigned elements skipped)

- **Date:** 2026-11-23
- **Status:** fixed 2026-11-24 (work/compiler-numeric-conv-20261124)
- **Area:** Rust seed interpreter, array methods
- **Found by:** web-render encode/readback lane (work/webrender-encode-readback-20261123)

## Repro

```simple
val px: [u32] = [0xffffffffu32, 0xffffffffu32, 3u32]
print px.sum()
```

| mode | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `0` (wrong) |
| `SIMPLE_EXECUTION_MODE=jit` | `8589934593` (right) |

The same happens on a 3600x3040 `[u32]` frame: the interpreter returns `0`, and the JIT returns the exact sum in 5.9 ms.

## Cause

`src/compiler_rust/compiler/src/interpreter_method/collections.rs`, `"sum"` arm (about line 743) only adds `Value::Int` elements. `[u8]`/`[u16]`/`[u32]`/`[u64]` elements are `Value::UInt`, so they are skipped without any error.

The sibling arm in `interpreter_helpers/method_dispatch.rs:544` does handle `Value::UInt`. The two arms disagree.

## Impact

- A silent wrong value with no error.
- `engine2d_pixel_checksum` (`src/lib/gc_async_mut/gpu/engine2d/backend.spl`) has to sum pixels in an interpreted loop. It cannot use `.sum()`: about 0.7 s per 4x frame instead of about 45 ms.

## Fix

- Add `Value::UInt { value, .. } => total += *value as i64` to the `collections.rs` arm, or route that arm to the `method_dispatch.rs` one.
- Add a spec covering `[u8]` and `[u32]` sums with high-bit values under both modes.
- Once a seed with the fix is deployed, the readback checksum can use `seg.sum()` for mixed blocks.

## Resolution (2026-11-24)

**Root cause.** The interpreter's `"sum"` arm in `interpreter_method/collections.rs` matched only
`Value::Int`. Typed unsigned arrays (`[u8]`/`[u16]`/`[u32]`/`[u64]`) hold `Value::UInt`
elements, so every one of them was skipped and the sum came out as 0. Float elements were
skipped as well, so `[1.5, 2.25].sum()` was also 0. The sibling arm in
`interpreter_helpers/method_dispatch.rs` and `rt_array_sum` (C and Rust lanes) were
already right.

**Fix.** The arm now adds `Value::UInt`. Like `rt_array_sum`, it sums ints with an i64
two's-complement wrap. Like `rt_array_sum`, it also promotes the result to float
(`float(int_sum) + float_sum`) when any element is `Float`/`Float32`. min/max were already
right for UInt (`numeric_ordering`). There is no array `product` method in the interpreter
or the JIT, so it needs no change.

**Evidence.** `src/compiler_rust/compiler/tests/unsigned_array_sum_engine_parity.rs` runs 16
rows (sum of every unsigned width with high-bit values, a high-bit and an overflowing `u64`
sum that wrap as i64, a single-element array, an empty
array, i64, and min/max) on both the interpreter and the JIT:

| seed | interpreter test | JIT test |
|---|---|---|
| base `91681a19c8c` | FAIL (row 1: `[u8]` sum) | pass |
| head | pass | pass |

Repro across engines, head seed (base interpreter printed `0` for every unsigned row):

| row | interpreter | JIT | native-build |
|---|---|---|---|
| `[255u8,255u8,3u8].sum()` | 513 | 513 | 513 |
| `[65535u16,65535u16,3u16].sum()` | 131073 | 131073 | 131073 |
| `[0xffffffffu32 x2, 3u32].sum()` | 8589934593 | 8589934593 | 8589934593 |
| `[5u64,7u64,0xffffffffu64].sum()` | 4294967307 | 4294967307 | 4294967307 |
| `[0x8000000000000000u64, 1u64].sum()` | -9223372036854775807 | -9223372036854775807 | -9223372036854775807 |
| `[0xffffffffffffffffu64, 2u64].sum()` | 1 | 1 | 1 |

**Still open (filed separately).** Compiled float-array sums still return a heap address:
`compiled_float_array_sum_reads_boxed_float_as_int_2026-11-24.md`. Also, native-build of a
program that uses `[T].min()` fails to link: `rt_array_min` has no C-runtime definition,
while `rt_array_max` links. That is pre-existing; base fails the same way.

**Float promotion: a behaviour change in the reference engine.** Interpreter `[f64].sum()`
used to return the Int 0. It now returns the float sum. A grep of `.sum()` over `src/lib`,
`src/app`, `test` and `examples` (71 sites) found one array consumer:
`src/lib/nogc_sync_mut/src/table.spl` group-by `"sum"`/`"mean"` over a `[f64]`. It got 0 there
before and now gets the real value. The other float `.sum()` sites are user class methods
(ndarray, `Vec3`), which this arm does not touch. The tab-bar page renders byte-identical on
the interpreter and the JIT, and on base and head.
