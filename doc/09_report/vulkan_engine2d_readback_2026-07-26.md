# Vulkan Engine2D Readback Evidence

- status: blocked
- reason: provider-incomplete-engine2d-closure
- host: Linux x86_64
- compiler: `build/gpu-goal/current/stage3/x86_64-unknown-linux-gnu/simple`
- compiler version: `simple-bootstrap 1.0.0-beta`
- execution evidence: not run

## Incremental Build

The cached Stage3 compiled all 184 modules in the Vulkan evidence closure after
`backend_directx.spl` reused the existing
`gc_async_mut.env.platform.is_windows` probe. The stub-enabled link produced
`build/vulkan-engine2d-readback/vulkan_evidence_native`, but that artifact is
not accepted as hardware evidence.

With `SIMPLE_NO_STUB_FALLBACK=1`, the same bounded build reached the linker with
zero unresolved Vulkan symbols. It failed on 70 unrelated optional runtime
symbols retained by the monolithic Engine2D closure:

| Family | Unresolved symbols |
|---|---:|
| OpenCL | 19 |
| OpenGL | 18 |
| oneAPI | 14 |
| Intel GPU | 11 |
| WebGPU | 8 |

## Resume

Provide a no-stub Vulkan-only closure/runtime lane, then run:

```sh
VK_DRIVER_FILES=/usr/share/vulkan/icd.d/nvidia_icd.json \
SIMPLE_EXECUTION_MODE=native \
sh scripts/check/check-vulkan-engine2d-readback.shs
```

Required pass evidence remains native Vulkan present/readback execution,
positive backend handle and device identity, zero pixel mismatches, and passing
strict/parity specs.
