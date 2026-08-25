# `use std.gpu.*` binds `rt_cuda_*` to the no-CUDA stub (device_count 0, cc (0,-3)) while direct module imports see 2 GPUs (2026-08-25)

**Status:** OPEN (seed dispatch defect, `src/compiler_rust`). **Binary:** Rust seed. **Host:** 2 live CUDA devices.

## Symptom
Same functions, different import path, different runtime binding:

| import | `gpu_device_count()` | `gpu_compute_capability(0)` |
|---|---|---|
| `use std.gc_async_mut.gpu_ops.*` (or `gpu_sffi`, `std.nogc_sync_mut.cuda.mod`) | **2** | (8, 6) |
| `use std.gpu.*` / `std.gc_async_mut.gpu.*` / `std.nogc_async_mut.gpu.*` (package `__init__`) | **0** | (0, **-3**) |

`-3` is the runtime's "built without the cuda feature" sentinel — but the same process, through
the direct import, reaches the real driver. No `use` warnings are emitted. `std.gpu_runtime`
standalone reports 2 (after the 2026-08-25 torch-gate fix).

## Impact
Every example and tutorial written against the documented `use std.gpu.*` surface silently
reports "no GPU" on a machine with two, and kernels launched through it write nothing
(`examples/08_gpu/simple_cuda_example/10.cuda_basic/12.First_Kernel` downloads all-0.0 while the
typed-transfer round-trip spec through the direct import passes 5/5).

## Reproduce (device-free discriminator: the -3 sentinel)
Two one-file probes in the scratchpad of the 2026-08-25 session (`p4` direct → 2, `p1` package →
0); minimal form:
```
use std.gpu.*
fn main():
    print "{gpu_device_count()} {gpu_compute_capability(0)}"     # 0 (0, -3)
```
vs. the same body with `use std.gc_async_mut.gpu_ops.*` → `2 (8, 6)`.

## Where to look
Package re-export resolution in the seed (`compiler_rust/compiler/src/interpreter_module/`) —
an `export use`/glob through `gpu/__init__.spl` apparently resolves the `extern fn rt_cuda_*`
declarations to a different (stub) provider than the direct module path does. Compare with
`runtime_native_gpu_stub.c` / `runtime_hosted_gpu_stubs.c` symbol precedence.
Unblocks the `use std.gpu.*` tutorial modules; until then examples import the concrete module.
