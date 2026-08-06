# gpu_memset_f32 discards its `value` argument and returns Ok(()) — blocked on a missing f32→u32 bitcast

- **Status:** OPEN (diagnosed, not fixed)
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
still missing is the value→bits conversion.

## The actual blocker: no working f32→u32 bitcast in the language

Both candidate routes are dead. Probed on `bin/simple` (Rust seed) this date:

| probe | result |
|-------|--------|
| `extern fn f32_to_bits(value: f32) -> u32` then call it | `semantic: unknown extern function: f32_to_bits` |
| `val v: f32 = 3.14` then `v.to_bits()` | `method 'to_bits' not found on type 'f64'` |

Two independent findings fall out of this:

1. **`f32_to_bits` is declared but has no runtime implementation.** It is
   `extern`-declared and called in production code that therefore cannot work:
   - `src/lib/nogc_sync_mut/src/hash.spl:15,251`
   - `src/lib/nogc_sync_mut/game_net/wire.spl:33,87` (also `f32_from_bits`)
   - `src/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl:9,104`
   No `f32_to_bits` / `f32_from_bits` entry exists in the seed's extern table
   (`src/compiler_rust/compiler/src/interpreter_extern/`) nor as an exported
   `rt_*` symbol in the runtime crate. The only hits in the Rust tree are inside
   `vendor/compiler_builtins`, which is not linked as a Simple extern.
2. **Simple's `f32` presents as `f64` at runtime** in this engine — the second
   probe's error names the receiver type as `f64` for a value declared `f32`.
   Any bitcast hook must therefore state its rounding contract explicitly
   (round-to-nearest f64→f32 before taking the bits), because the hook will
   receive an f64, not an f32.

## Suggested fix (decided question, not yet implemented)

Implement `f32_to_bits` / `f32_from_bits` for real — as a general float
primitive, NOT parked in the CUDA module — registering in all four seed sites
that an extern needs (`interpreter_extern/mod.rs`, the backing `_fn`,
`codegen/runtime_sffi.rs`, `interpreter_eval.rs`) plus the runtime `rt_*` export.
That unblocks the three files above as well as this bug. Then:

```
fn gpu_f32_fill_pattern(value: f32) -> i64:
    f32_to_bits(value).to_i64()

fn gpu_memset_f32(ptr: GpuPtr, value: f32, count: i64) -> Result<(), GpuError>:
    gpu_memset_d32(ptr, gpu_f32_fill_pattern(value), count)
```

with a host-side spec asserting the IEEE-754 oracle (3.14f → 0x4048F5C3 =
1078523331; 1.0f → 0x3F800000; -0.0f → 0x80000000) and the rounding contract.

Deliberately NOT done here: adding a one-off `rt_f32_fill_bits` inside
`cuda_runtime.rs` just to close this call site. That would park a general
float-bitcast primitive in the CUDA module, and its f64→f32 marshalling could
not be verified — bootstrap stage 3 is blocked, so no self-hosted binary can be
redeployed to exercise the native SFFI path.

## What was NOT verified

No on-device execution of anything in this report. `cuInit` returns 3
(`CUDA_ERROR_NOT_INITIALIZED`) in this process even though two real GPUs
(RTX A6000 + TITAN RTX, driver 580.126.16) are present and `libcuda.so.1`
dlopens. No `cuMemsetD32_v2` call was ever issued against a real allocation.
