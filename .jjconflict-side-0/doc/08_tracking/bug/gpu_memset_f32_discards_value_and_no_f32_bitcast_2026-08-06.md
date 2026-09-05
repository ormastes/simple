# gpu_memset_f32 discards its `value` argument and returns Ok(()) — blocked on a missing f32→u32 bitcast

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Date:** 2026-08-06
- **Severity:** high — silently-wrong success
- **Sites:** `src/lib/gc_async_mut/gpu_ops.spl`, `src/lib/gc_async_mut/gpu_api.spl`
- **Related (FIXED, same family):** `gpu_memset_i32` byte-granularity defect —
  fixed by routing through the new `cuMemsetD32_v2` primitive `rt_cuda_memset_d32`.

## Symptom

```
fn gpu_memset_f32(ptr: GpuPtr, value: f32, count: i64) -> Result<(), GpuError>:
    """Memset f32 device memory."""
    gpu_memset(ptr, 0, count * 4)
```

`value` is never read. A caller asking to fill a buffer with 3.14 gets zeros —
and gets `Ok(())`. Both copies of the wrapper have the identical body.

## Why this is not a one-line fix

The obvious repair — forward `value` to `gpu_memset` — cannot work at any value.
`gpu_memset` is BYTE granularity (CUDA `cuMemsetD8_v2`, which truncates its value
to eight bits and replicates that byte). Per the CUDA Driver API:

```
CUresult cuMemsetD8_v2 (CUdeviceptr dstDevice, unsigned char uc, size_t N)   # N BYTES
CUresult cuMemsetD32_v2(CUdeviceptr dstDevice, unsigned int  ui, size_t N)   # N 32-bit ELEMENTS
```

IEEE-754 single precision for 3.14f is `0x4048F5C3` — not byte-uniform, so no
`cuMemsetD8` call can produce it. The correct fill therefore requires the 32-bit
primitive **and** the f32 bit pattern of `value`.

The fill path is no longer the blocker: `gpu_memset_d32` /
`cuda_memset_d32` / `rt_cuda_memset_d32` (`cuMemsetD32_v2`) now exist. What is
was believed missing was the value→bits conversion — see the CORRECTION below:
that conversion already existed.


## CORRECTION 2026-08-07 — the "no f32 bitcast exists" blocker was WRONG

The section that used to stand here claimed `f32_to_bits` / `f32_from_bits` have
no implementation anywhere and that a NEW runtime extern had to be registered in
four seed sites. **That is false, and was false when written.**

`src/lib/common/binary_io.spl` already implements `f32_to_bits`, `f64_to_bits`,
`f32_from_bits` and `f64_from_bits` in pure Simple, layered on `spl_f64_to_bits`
(the one natively linked float primitive). No new extern is needed. Commit
`8554402f091` superseded this doc by routing `hash.spl` at
`use std.common.binary_io.{f32_to_bits, f64_to_bits}`.

### Why the original probe read as a dead end

The probe in the table above declared `extern fn f32_to_bits(...)` and called it.
That declares a NEW unbacked extern and shadows the real pure-Simple function; an
unbacked extern resolves to nil. The probe therefore measured its own extern
declaration, not the library. `f32_to_bits` was never missing — it was never
imported. The correct form is `use std.common.binary_io.{f32_to_bits}`.

### Verification (2026-08-07, `bin/simple run`, INTERPRET and JIT, both agree)

| input | measured | IEEE-754 oracle | |
|-------|----------|-----------------|---|
| `1.0f32`   | 1065353216 | `0x3F800000` | PASS |
| `3.14f32`  | 1078523331 | `0x4048F5C3` | PASS |
| `-0.0f32`  | 2147483648 | `0x80000000` | PASS (sign bit survives) |
| `1e-40f32` | 71362      | `0x000116C2` | PASS (subnormal) |

Round-trip `f32_from_bits(0x3F800000)` returns `1.0`.

**Also corrected:** the subnormal constant quoted for `1e-40f32` in
`src/lib/nogc_sync_mut/src/hash.spl`'s header comment (and repeated in downstream
notes) was `0x00011692`. The true value is `0x000116C2` = 71362, confirmed
against `struct.pack('<f', 1e-40)`. The library was right; the quoted oracle was
wrong. Never fix an implementation to match an unverified constant.

### What is genuinely still open for `gpu_memset_f32`

Only the wiring, and it is now a small change with no blocker in front of it:

```
use std.common.binary_io.{f32_to_bits}

fn gpu_memset_f32(ptr: GpuPtr, value: f32, count: i64) -> Result<(), GpuError>:
    gpu_memset_d32(ptr, f32_to_bits(value).to_i64(), count)
```

Finding 2 of the removed section survives and still matters: **Simple's `f32`
presents as `f64` at runtime in this engine** (`v.to_bits()` on an `f32`-declared
value reports the receiver as `f64`). `binary_io.f32_to_bits` already handles
this — it takes the f64, rounds to nearest f32, and extracts those bits — which
is why the table above passes. Any *new* bitcast hook would have to state the
same rounding contract; there is no reason to add one.

### Status

- Original blocker claim ("no f32→u32 bitcast in the language"): **DISPROVEN**.
- `gpu_memset_f32` discarding `value`: **still OPEN**, now unblocked.
- Doc retained rather than deleted so the false blocker is not rediscovered.

## What was NOT verified

No on-device execution of anything in this report. `cuInit` returns 3
(`CUDA_ERROR_NOT_INITIALIZED`) in this process even though two real GPUs
(RTX A6000 + TITAN RTX, driver 580.126.16) are present and `libcuda.so.1`
dlopens. No `cuMemsetD32_v2` call was ever issued against a real allocation.
