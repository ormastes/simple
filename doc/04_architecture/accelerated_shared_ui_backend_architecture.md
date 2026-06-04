<!-- codex-design -->
# Accelerated Shared UI Backend Architecture

Date: 2026-06-03
Status: Candidate architecture pending requirement selection

## Layer Stack

```
Application UI model
  -> Shared semantic UI interface
  -> Host adapters: TUI, pure Simple GUI, pure Simple web, Tauri, Electron, NodeJS/browser
  -> Shared web render interface
  -> Pure Simple web renderer
  -> Engine2D render interface
  -> 2D backend sessions: CPU scalar, CPU SIMD, CUDA, OpenCL, Vulkan, Metal, WebGPU
  -> Compiler offload: tagged Simple kernels -> backend artifacts
```

## Capsules

| Capsule | Responsibility | Must Not Own |
|---|---|---|
| `ui.semantic` | Widget tree, commands, focus, events, accessibility state | Host IPC, pixels, GPU state |
| `ui.host` | TUI, Tauri, Electron, NodeJS/browser, pure Simple host transport | Semantic policy |
| `web.render` | HTML/snapshot/patch/input render artifacts | Window-manager authority |
| `engine2d.render` | 2D primitives, readback, capture, equality evidence | Compiler codegen |
| `gpu.compute` | Runtime sessions, device capabilities, artifact load/submit/sync/readback | Language syntax |
| `compiler.offload` | GPU tags, kernel subset checking, PTX/SPIR-V/OpenCL C/Metal artifact emission | Runtime probing |
| `optimization.provider` | SIMD width, shader specialization, pipeline cache, PGO facts | Rendering policy |

## OpenCL Like CUDA Support

CUDA remains the NVPTX/PTX target in `src/compiler_rust/compiler/src/codegen/llvm/gpu.rs`.
OpenCL should be added as a sibling target, not as a CUDA branch:

1. Extend the GPU target model with `OpenCL(id)` and `Auto([CUDA, OpenCL, ...])`.
2. Extend `gpu_checker.spl` with target capability checks for address spaces,
   barriers, subgroup assumptions, unsupported intrinsics, and scalar/vector
   type legality.
3. Add an OpenCL artifact emitter path that can produce either OpenCL C source
   for runtime build or SPIR-V for implementations that accept the OpenCL
   SPIR-V environment.
4. Complete the lower OpenCL runtime layer first:
   `src/runtime/runtime_simd_dispatch.c` and
   `src/lib/nogc_sync_mut/gpu/engine2d/sffi_opencl.spl` must implement context,
   queue, program build, kernel creation, enqueue, finish, and typed errors.
5. Reuse `opencl_session.spl` and `generated_kernel_dispatch.spl` for
   load/submit/sync/readback evidence.
6. Require checksums or typed pixel evidence before reporting device execution.

## Tagged Simple Offload

Tags should be declarative and evidence-producing:

```simple
@gpu(target="auto", backends=["cuda", "opencl"], op="engine2d.fill")
kernel fn fill_rect_kernel(args: FillArgs):
    ...
```

The compiler records the selected backend, emitted artifact format, entrypoint,
ABI layout, and unsupported feature diagnostics. Runtime selection may fall back
only when the report preserves the failed preferred backend and reason.

## Performance Evidence

Every backend comparison report must include:

- cold start and warm start;
- binary/package size;
- p50/p95 frame time and input-to-paint latency;
- max RSS;
- artifact compile/load/submit/sync/readback timing;
- selected backend, device, target arch, feature flags, and fallback reason;
- checksum or pixel/capture proof for rendering claims.

The normalized comparison harness sits above existing focused probes. It should
reuse `scripts/check/check-startup-size-performance-audit.shs`,
`scripts/check/check-web-baremetal-size-audit.shs`, `test/perf/tauri_equiv/`, and
`test/perf/graphics_2d/`, but convert their outputs into one
`BackendComparisonSample` schema. Backend-specific probes may keep their native
formats, but release evidence must include the normalized schema.

## Startup And Size Strategy

- Production wrappers execute cached compiled artifacts, not raw source
  entrypoints.
- Shell adapters keep host IPC and webview boot code thin; shared render logic
  stays in Simple artifacts.
- Hot request handlers may not perform full-tree scans, repeated file rereads,
  subprocess retries, or driver probing. Capability probes run at startup or
  explicit reindex/probe time and are cached with invalidation metadata.
