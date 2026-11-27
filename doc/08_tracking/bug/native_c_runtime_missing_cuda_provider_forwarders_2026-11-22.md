# Native C runtime has no forwarders for 28 CUDA externs; native programs using std device queries fail to link (2026-11-22)

**Status:** VERIFIED 2026-11-26 (gap tracked as cuda_module_get_function_cstr_text_abi_2026-11-26). **Found:** 2026-11-22 (work/cuda-runtime-bugs). **Component:** `src/runtime/runtime_dynload.c` (GPU provider dispatch).

## Symptom
integ25 Stage 2 (sha256 `ef46f0d2ab4274c4`), `native-build --backend=llvm --entry-closure` of
`use std.gc_async_mut.gpu_ops.*` + `gpu_init()` / `gpu_device_count()` /
`gpu_device_compute_capability(0)`:

```
ld.lld: error: undefined symbol: rt_cuda_device_compute_capability
ld.lld: error: undefined symbol: rt_cuda_device_get
ld.lld: error: undefined symbol: rt_cuda_get_error_string
```

## Cause
`simple_cuda_required[]` (runtime_dynload.c:199) requires the provider DSO to export these
symbols, but only a subset has a `GPU_CALLn` forwarder in the base executable
(runtime_dynload.c:1688-1712). Static diff of the `extern fn rt_cuda_*` set in
`src/lib/nogc_sync_mut/cuda/sffi.spl` against the forwarders: 28 externs have no definition in
the C runtime:

rt_cuda_ctx_create rt_cuda_ctx_destroy rt_cuda_ctx_set_current rt_cuda_ctx_synchronize rt_cuda_device_compute_capability rt_cuda_device_get rt_cuda_device_identity rt_cuda_device_name rt_cuda_f64_binary_op rt_cuda_f64_minmax rt_cuda_f64_scalar_div rt_cuda_f64_slice_1d rt_cuda_f64_slice_2d rt_cuda_f64_sum rt_cuda_f64_sum_axis rt_cuda_get_error_string rt_cuda_launch_kernel rt_cuda_launch_kernel_name rt_cuda_memcpy_dtod rt_cuda_memcpy_htod rt_cuda_mem_free rt_cuda_memset rt_cuda_module_get_function rt_cuda_module_load rt_cuda_module_load_data rt_cuda_module_load_data_bytes rt_cuda_module_unload rt_cuda_sync 

Of these, 16 are already in `simple_cuda_required[]` (the provider must export them), so a
forwarder is a mechanical `GPU_CALLn` row each; the other 12 (`f64_*`, `module_load`,
`module_get_function`, `launch_kernel`, `device_identity`, `module_load_data`) need an
ABI decision first.

## Acceptance
Native-build the fixture above with a provider (`build/sffi/libsimple_gpu_cuda.so` via
`scripts/build/build_simple_runtime_sffi.shs`, `SIMPLE_CUDA_PROVIDER_PATH` +
`SIMPLE_CUDA_PROVIDER_SHA256`) and see the live count and capability; without a provider it must link and report 0 devices.
Extend `scripts/check/check-gpu-provider-dynload-registry.shs` to cover the new forwarders.

## Also seen on the same Stage 2 (not chased)
- `use std.cuda.*` (→ `nogc_async_mut/cuda/mod.spl`) fails HIR: `unresolved name: id` at
  `mod.spl:688:17` and `Device.CUDA pattern has 1 slot(s), declaration has 0`.
- cranelift: `Failed to compile function: lib.gc_async_mut.gpu_ops.gpu_load_f32`.

## Resolution (2026-11-26, work/bug-cuda-native-20261126) — verified on GB10

- `runtime_dynload.c` forwarded 27 of the 28 externs (all 28 since `cuda_module_get_function_cstr_text_abi_2026-11-26`) to the CUDA provider
  (`GPU_CALLn` rows plus hand-written `f64_slice_2d`, `launch_kernel`,
  `launch_kernel_name` and `device_name`). `device_name` copies the
  provider string into a per-thread runtime-owned buffer while the call is
  pinned, so no provider-owned pointer escapes. A first call that finds the
  provider LOADING yields (`sched_yield`) until the loader publishes a
  terminal state, instead of reporting "unavailable". The loader thread
  re-entering its own load still gets "unavailable", and a `pthread_atfork`
  child handler fails a load that was in flight at `fork`, so neither can
  wait forever.
  Each unavailable value is the matching Rust `not(feature = "cuda")` twin's:
  -3, or 0 for `device_compute_capability`/`device_identity`, or `"No CUDA"`
  for `device_name`. `rt_cuda_get_error_string` is a pure C copy of the Rust
  code→name table, so it needs no provider. `module_load` and
  `module_load_data` take a Simple `text` as (bytes, len): both have a
  `text_extern_abi.spl` row, so native codegen splits them. `simple_cuda_required[]` is unchanged.
- **Gap, closed 2026-11-26** (`cuda_module_get_function_cstr_text_abi_2026-11-26`):
  `rt_cuda_module_get_function` is now forwarded too, so all 28 are. It keeps
  the C-string ABI: native codegen passes this `text` argument as one
  `rt_interp_cstr` pointer, because it has no `text_extern_abi.spl` row. See
  that bug's own doc.
- **Second root cause, found end to end:** the provider DSO itself could not be
  `dlopen`ed. `runtime_timestamp.c` used initial-exec TLS, which marks
  `libsimple_runtime.so` `DF_STATIC_TLS`. glibc then needs the whole ~72 KiB
  TLS block in the static surplus, and fails with `cannot allocate memory in
  static TLS block`. The Rust crate now builds that file with
  `SIMPLE_RUNTIME_DYNAMIC_TLS`. The core-C/Stage4 archive keeps initial-exec.
- Red→green:
  - `scripts/check/check-gpu-provider-dynload-registry.shs` was extended with
    device-query, f64 and module dispatch. Red: 7 undefined symbols. Green after
    the fix.
  - `scripts/check/check-cuda-device-query-native.shs <integ25-stage2 native
    build of src/app/test/cuda_device_query_probe.spl> <provider .so> GB10`
    reports `PASS`, with `NVIDIA GB10 capability=121`. With no provider every
    value is a clean sentinel (init=3). With `SIMPLE_CUDA_LIB` set to a missing
    file it reports init=303. Every run exits 0, and the core-C and Rust lanes
    print identical lines.
- The filed std shape (`use std.gc_async_mut.gpu_ops.*`: `gpu_init`, `gpu_device_count`,
  `gpu_device_name`, `gpu_device_compute_capability`) is
  `src/app/test/cuda_std_device_query_probe.spl`. integ25 Stage 2 builds it with
  `--backend llvm --source src/lib --source src/app --entry-closure`, and it links:
  - with the provider: `CUDA_STD_QUERY init_ok=true count=1 name=NVIDIA GB10 capability=12.1`
  - with no provider: `init_ok=false count=0 name=No CUDA capability=0.0`
  - with libcuda missing: `init_ok=false count=0 name=Unknown capability=-30.-3`.
    `gpu_ops` splits the raw -303 as `/10`, `%10`; that is pre-existing gpu_ops
    behaviour, not this fix.

  Every run exits 0.
- **Lane parity, all three rows measured.** Each row is a run, not a reading of
  the source:
  - GPU and no-driver: the C forwarder output equals a direct dlopen of the Rust
    provider.
  - No provider: the C forwarder output equals a binary linked against the integ25
    authority, whose Rust non-cuda twins own `rt_cuda_*`. Both print
    `init=3 count=0 device=-3 name=No CUDA capability=0`.
- That last binary was the second bug,
  `native_link_rt_cuda_init_never_opens_libcuda_2026-11-22`: in the
  `--runtime-path` lane the provider was never consulted. That lane is now
  fixed by building the authority with feature `cuda` (see that bug).
- The seed's core-C lane (`SIMPLE_NATIVE_BUILD_RUST=1`, `tools.rs`
  `build_c_runtime_library`) still has no `runtime_dynload.c`, so there
  `rt_cuda_init` itself is undefined. This is a separate seed-lane gap, and the list
  was not widened here.
