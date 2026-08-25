# GPU / CUDA programming in Simple — practical guide (2026-08-25)

Audience: anyone writing a GPU kernel in Simple. Companion to `gpu_api.md` (API reference)
and `gpu_backend_hardening.md`. Worked tutorial: `examples/08_gpu/simple_cuda_example/`
(the `ormastes/cuda_exercise` CUDA workbook re-implemented in Simple, module by module).

## Three surfaces, pick by need

| surface | import | what it is | when |
|---|---|---|---|
| `std.cuda` | `use std.cuda.*` | thin i64-handle wrapper over the CUDA **driver** API (dlopened `libcuda.so.1`, no toolkit needed) | device queries, raw memory, PTX modules |
| `std.io` CUDA SFFI | `use std.io.{CudaPtr, CudaModule, CudaFunc, cuda_compile, cuda_launch, ...}` | typed handles + launch config + honest default stream | launching a PTX kernel with parameters |
| `std.gpu` / `gpu_ops` | `use std.gc_async_mut.gpu_ops.*` (see caveat) | backend-agnostic `Result<_, GpuError>` API, typed upload/download, kernel-side builtins (`gpu_global_id`, `gpu_atomic_add_*`, `gpu_shared_*`) and `cpu_kernel_run_1d` emulation | tutorial code, tests that must run without a device |

**Caveat (open bug):** on the current seed, `use std.gpu.*` through the package `__init__` binds
`rt_cuda_*` to the no-CUDA stub and reports 0 devices / compute capability `(0, -3)`; the direct
module import `std.gc_async_mut.gpu_ops.*` sees the real driver. See
`doc/08_tracking/bug/std_gpu_package_import_binds_cuda_externs_to_nocuda_stub_2026-08-25.md`.

## 1. Query the device

<!--sdoctest:ignore-begin-->

```simple
use std.cuda.{cuda_available, cuda_init, cuda_device_count, cuda_get_device_name, cuda_device_compute_capability}

fn main():
    if not cuda_available():
        print "no CUDA driver"
        return
    cuda_init()
    for d in 0..cuda_device_count():
        print "{d}: {cuda_get_device_name(d)} cc={cuda_device_compute_capability(d)}"
```

Measured on the 2-GPU dev host: `0: NVIDIA RTX A6000 cc=86`, `1: NVIDIA TITAN RTX cc=75` —
`cuda_device_compute_capability` returns the capability **packed** as one i64 (86 = sm_86).

## 2. Memory round-trip (typed helpers)

```simple
use std.gc_async_mut.gpu_ops.{gpu_set_device, gpu_alloc, gpu_upload_f32, gpu_download_f32, gpu_free}

fn main():
    gpu_set_device(0)
    val n = 2048
    val d = gpu_alloc(n * 4).unwrap()
    val host = [for i in 0..n: (i as f32) + 0.5]
    gpu_upload_f32(d, host).unwrap()
    val back = gpu_download_f32(d, n).unwrap()
    print "{back[0]} {back[n - 1]}"      # 0.5 2047.5
    gpu_free(d)
```

Until 2026-08-25 these helpers passed the interpreter's tagged `Vec<Value>` pointer as raw
bytes — silent corruption below ~1 KB, SEGV above. They now stage through a raw buffer;
the guard is `test/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.spl`.

## 3. Launch a PTX kernel with parameters

```simple
use std.io.{cuda_set_device, cuda_alloc, cuda_copy_to_device, cuda_copy_from_device,
            cuda_compile, cuda_get_kernel, cuda_launch_config_1d, cuda_launch, cuda_sync, cuda_free}

# kernel written in PTX (or produced by the Simple->PTX backend, see §5)
val PTX = "..."     # .entry square(.param .u64 p, .param .u32 n) ...

fn main():
    cuda_set_device(0)
    val n = 256
    val buf = cuda_alloc(n * 4)
    val module = cuda_compile(PTX)
    val k = cuda_get_kernel(module, "square")
    cuda_launch(k, cuda_launch_config_1d(n, 64), [buf.handle, n])
    cuda_sync()
    val bytes = cuda_copy_from_device(buf, n * 4)
    cuda_free(buf)
```

`cuda_launch` builds the driver's `void**` parameter block for you. Streams are the honest
**default stream** (`CudaStream` handle 0): the runtime exposes no `cuStreamCreate`, so there is
no async overlap yet, and there are no CUDA events. The kernel-launch grammar
`k<<<grid: g, block: b>>>(args)` has no `stream:` slot —
`doc/08_tracking/bug/kernel_launch_grammar_no_stream_slot_2026-08-25.md`.

<!--sdoctest:ignore-end-->

## 4. Device-free development: `cpu_kernel_run_1d`

Every kernel-side builtin (`gpu_global_id`, `gpu_local_id_x`, `gpu_syncthreads`,
`gpu_atomic_add_i32`, `gpu_shared_load_f32`, ...) has a CPU emulation, so a kernel body can be
run on the host to check indexing logic. This is what the tutorial READMEs' `sdoctest` blocks
use — they must be deterministic, so never print device names or timings in them.

```sdoctest
>>> use std.gc_async_mut.gpu_ops.{cpu_kernel_run_1d}
>>> fn noop():
...     pass_dn
>>> print "{cpu_kernel_run_1d(10, 4, noop)} invoked, {cpu_kernel_run_1d(0, 4, noop)} for an empty range"
10 invoked, 0 for an empty range
```

(`10` elements at block size `4` dispatch `3` blocks; the emulator invokes exactly the 10
in-range work-items — the tail guard `if i < n` that CUDA code needs is applied for you.)

For 2-D/3-D layouts use `gpu_launch_emulated((gx, gy, gz), (bx, by, bz), kernel)` — the host
meaning of `kernel<<<grid, block>>>()`: every `gpu_block_id_*`, `gpu_local_id_*`,
`gpu_block_dim_*`, `gpu_grid_dim_*` and `gpu_global_id_*` reflects the current work-item, so
the tutorial's `vector_add_2d` / tiled-matmul index math runs unchanged on the CPU
(`test/01_unit/lib/gpu/gpu_launch_emulated_3d_spec.spl`). Serial semantics: shared-memory
exchange across threads is not modelled (`gpu_syncthreads` is a no-op).

## 5. Same code, different backend

`examples/08_gpu/backends/` runs one SVM-G program on CUDA, Vulkan or Metal; the only thing
that changes is the `gpu:` section of `simple.sdn` (`backend: cuda | vulkan | metal | auto`).
Metal on Linux answers `skip:metal-unavailable-not-macos` — a skip, never a fake pass.
Vulkan currently initialises under the spec runner but not under `bin/simple run`
(`doc/08_tracking/bug/vulkan_instance_init_fails_under_run_but_not_test_2026-08-25.md`).
Simple→PTX codegen for `@gpu("cuda")` functions exists (`compiler_rust/.../codegen/llvm/gpu.rs`),
but the seed cannot drive the pure-Simple HIR lowering for it yet
(`doc/08_tracking/bug/cuda_jit_hello_lane_lower_module_missing_import_2026-08-25.md`).

## 6. What maps to what (from the CUDA workbook)

| CUDA workbook module | Simple | status |
|---|---|---|
| 11 Foundations, 12 First kernel, 15 Unit testing, 16 Error handling, 17 Memory hierarchy, 18 Thread hierarchy, 19 Memory API | `std.cuda` + `gpu_ops` | ported, `main.spl` + `spec.spl` + doctest |
| 21 Sync & atomics, 23 Shared memory, 24 Coalescing | `gpu_atomic_*`, `gpu_shared_*` | ported |
| 22 Streams & async | default stream only | ported honestly (no overlap) |
| 27 Multi-GPU | `cuda_set_device` per device | ported |
| 25 Dynamic parallelism, 26 Cooperative groups, 31–38 vendor libraries, 41–47 PTX/intrinsics/graphs/IPC/VMM | — | README-only, states there is no Simple equivalent |

## Testing rules that bite here
- Real-hardware assertions go behind `SIMPLE_CUDA_TEST=1`; device-free checks (extern ABI,
  config parsing, index math) must run everywhere.
- Never run two `bin/simple test <dir>` in parallel (shared test DB). One spec at a time.
- A tutorial checkout with its own `.git` inside the repo makes the seed resolve the stdlib from
  a *different* worktree (`compiler_rust` workspace-boundary walk) — your stdlib edits will look
  invisible. Verify with `strace -e openat` which `src/lib` is opened.
