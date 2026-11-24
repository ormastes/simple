# Interpreter: `[u32].sum()` returns 0 (unsigned elements skipped)

- **Date:** 2026-11-23
- **Status:** open
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
