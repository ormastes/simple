# Vulkan Engine2D Readback Evidence

- status: blocked
- reason: cached-stage3-readback-aggregate-abi
- host: Linux x86_64
- compiler: `build/gpu-goal/current/stage3/x86_64-unknown-linux-gnu/simple`
- compiler version: `simple-bootstrap 1.0.0-beta`
- execution evidence: initialization and strict creation pass; readback crashes

## Incremental Build

The cached Stage3 compiled all 184 modules in the Vulkan evidence closure after
`backend_directx.spl` reused the existing
`gc_async_mut.env.platform.is_windows` probe. The stub-enabled link produced
`build/vulkan-engine2d-readback/vulkan_evidence_native`, but that artifact is
not accepted as hardware evidence.

With `SIMPLE_NO_STUB_FALLBACK=1`, the same bounded build reached the linker with
zero unresolved Vulkan symbols when using the core-C runtime. It failed on 70
unrelated optional runtime symbols retained by the monolithic Engine2D closure:

| Family | Unresolved symbols |
|---|---:|
| OpenCL | 19 |
| OpenGL | 18 |
| oneAPI | 14 |
| Intel GPU | 11 |
| WebGPU | 8 |

The existing
`build/todo580_transient_scope_runtime_v7/libsimple_native_all.a` exports all
five families plus 88 Vulkan symbols. Three bounded attempts supplied that
archive by relative CLI path, absolute CLI path, and direct
`SIMPLE_RUNTIME_PATH`. The cached Stage3 still selected `core-c-bootstrap` and
did not admit the archive, so no provider-complete executable was produced.

An isolated incremental `simple-runtime` build with `vulkan,cuda` produced a
non-stub Vulkan provider. Manual no-stub linking with the emitted 184-module
Simple archive succeeded. On the NVIDIA ICD, the native probe then reported:

```text
status=Initialized
compute=true
graphics=true
reason=Vulkan initialized
```

`backend_probe_initialized` now performs the enum comparison in its owner
module. The same executable reports `vulkan_available=true`,
`strict_create_status=pass`, and `backend_name=vulkan`.

The first cross-module `Engine2DReadback` return is then corrupted:
`pixels.len()` is `-1`, handle and device identity are zero, and GDB records a
segfault in `write_u32_pixels`. No readback pass is claimed.

Disassembly identifies the cause: the returned class pointer carries
`TAG_HEAP`, but LLVM aggregate field reads and writes used it directly.
`untag_aggregate_base_ptr` now conditionally strips that tag before field GEP.
The focused x86_64/RV32 IR regression passes 2/2. The cached Stage3 predates
this source fix, so hardware evidence remains blocked pending a bounded
source-matched compiler build.

## Resume

Deploy the source fix described in
`doc/08_tracking/bug/native_engine2d_readback_aggregate_abi_2026-07-26.md`
through the bounded incremental compiler lane, then run:

```sh
VK_DRIVER_FILES=/usr/share/vulkan/icd.d/nvidia_icd.json \
SIMPLE_EXECUTION_MODE=native \
sh scripts/check/check-vulkan-engine2d-readback.shs
```

Required pass evidence remains native Vulkan present/readback execution,
positive backend handle and device identity, zero pixel mismatches, and passing
strict/parity specs.
