# GUI/Web Host-GPU Platform Evidence Matrix

Date: 2026-06-14
Status: superseded/merged into
`doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`
for active parallel-agent routing, and into
`doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md`
for current Linux Vulkan, macOS Metal, and Windows D3D12 RenderDoc/render-log
execution. Keep this file as a historical host-GPU queue/readback matrix and
as detailed background for platform-specific device-readback semantics.

Current routing update, 2026-06-27:

- Spark agents may collect platform logs and readiness/provenance rows from
  this matrix, but they do not promote a backend to production proof.
- Normal/high-capability review must accept native device-readback, RenderDoc
  or GPU-debugger artifacts, native render-log comparison, and no raw `rt_*` or
  direct backend-poke source changes before any platform is marked complete.
- Linux Vulkan strict render-log comparison is sequenced after browser backing,
  direct Electron/Chrome/Simple ARGB comparison, and valid Chrome/Electron/Simple
  `.rdc` artifacts with `RDOC` magic.
- macOS Metal and Windows D3D12 completion claims must use the current
  platform runbook and evidence keys; this matrix alone is not acceptance
  evidence.
- Retained 4K/8K showcase performance is tracked in the 2026-06-27 parallel
  plan as its own lane and must not be inferred from queue/readback rows.

Host-scope update, 2026-06-28:

- The current Linux repo session cannot complete macOS Metal or Windows
  D3D12/PIX validation. Those lanes are postponed from this host.
- Linux agents may continue shared wrapper/spec hardening and Linux Vulkan
  evidence work only when the host has real GUI/Vulkan/RenderDoc access.
- macOS Metal acceptance requires native Darwin evidence from Metal tooling and
  GPU capture/readback logs.
- Windows D3D12 acceptance requires native Windows evidence from D3D12
  readback, Chrome/Electron D3D12 backing, and PIX or equivalent GPU-debugger
  artifacts.
- Imported macOS/Windows evidence must be reviewed before any overall
  GUI/Web/2D platform completion claim.

## Scope

Track the remaining host-specific proof needed for production-level GUI/web 2D
Engine2D queue/readback evidence after the Linux Vulkan/CUDA/OpenCL work. This is a
coordination plan for parallel agents; do not use it as proof by itself.

## Canonical Gate

Run from repo root:

```sh
BUILD_DIR=build/production_gui_web_host_gpu_queue_readback_<agent> \
SIMPLE_BIN=src/compiler_rust/target/debug/simple \
SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

The report is:

```text
doc/09_report/production_gui_web_host_gpu_queue_readback_YYYY-MM-DD.md
```

## Parallel Work Items

### Linux Vulkan/CUDA/OpenCL Agent

Owns:
- `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
- `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_*readback*`
- BrowserBackend runtime queue specs.

Acceptance:
- `browser_first_backend_handle` is positive for the BrowserBackend production
  frame, propagated from the Engine2D backend readback receipt.
- `browser_first_readback_pixel_count`, `browser_first_readback_checksum`, and
  `browser_first_readback_reason` are propagated from the typed
  `Engine2DReadback` receipt.
- Synthetic Vulkan handle `7` stays limited to isolated runtime queue roundtrip
  tests.
- `browser_first_gpu_readback_source=device_readback`.
- `browser_first_payload_size`, `browser_first_payload_hash`, and
  `browser_first_payload_text` prove the actual BrowserBackend frame packet
  carried payload receipt data.
- `browser_first_render_under_budget=true` and
  `browser_second_render_under_budget=true` prove conservative first-frame and
  cached-frame timing budgets for the production BrowserBackend probe.
- `readback_vulkan_verdict=pass`.
- `readback_cuda_verdict=pass` on CUDA-capable Linux.
- `readback_opencl_verdict=pass` on OpenCL-capable Linux.
- Linux Vulkan/CUDA/OpenCL GUI/web queue integration exits zero when positive
  BrowserBackend backend handle, typed frame payload receipt, timing budgets,
  typed readback metadata, same-frame `device_readback`, Vulkan readback, CUDA
  readback, and OpenCL generated 2D readback all pass. The full host-GPU
  platform matrix remains incomplete until Metal, ROCm/HIP, and native DirectX
  device-readback evidence pass.
  Synthetic handles remain limited to isolated runtime queue roundtrip tests.

### Linux OpenCL Matrix Notes

OpenCL generated 2D readback is a required local Linux child check in the
production wrapper. The wrapper uses
`scripts/check/check-opencl-generated-2d-readback.shs` and requires a real
`readback-pixels-matched` pass rather than CPU-mirror equivalence. Hosts without
an OpenCL loader/probe/toolchain must either provide that runtime or explicitly
run a narrower non-production wrapper lane; absence of OpenCL is not a GUI/web
production PASS on this Linux matrix.

### macOS Metal Agent

Owns only Metal host evidence and reports.

Commands:

```sh
sh scripts/check/check-metal-generated-2d-readback.shs
BUILD_DIR=build/production_gui_web_host_gpu_queue_readback_macos \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Host requirements:
- macOS/Darwin host.
- `xcrun metal` and `xcrun metallib` or equivalent tools.
- `system_profiler SPDisplaysDataType`.
- Working `bin/simple` or `SIMPLE_BIN`.

Acceptance:
- Metal direct readback report is `pass`.
- Production wrapper records Metal as `pass` on macOS, not Linux unavailable.

### ROCm/HIP Agent

Owns only ROCm/HIP host evidence and reports.

Commands:

```sh
HIP_ARCH=${HIP_ARCH:-gfx1100} sh scripts/check/check-rocm-generated-2d-readback.shs
BUILD_DIR=build/production_gui_web_host_gpu_queue_readback_rocm \
SIMPLE_BIN=bin/simple \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Host requirements:
- AMD ROCm-capable host/device.
- `hipcc`, `rocminfo`, ROCm loader libraries.
- Verified HSACO for the selected `HIP_ARCH`.

Acceptance:
- ROCm generated 2D readback has a real pass path instead of
  `missing-rocm-submit-readback-harness`.
- Production wrapper records ROCm/HIP as `pass` on a ROCm host.

### Windows/DirectX Agent

Owns only DirectX evidence planning unless a Windows host is available.

Current state:
- DirectX is included in the production queue/readback wrapper as a native
  child probe, but it is not a production DirectX pass unless
  `readback_directx_native_verdict=pass` and `directx_native_gate_status=pass`.
- Linux DXVK setup exists but is setup/plumbing, not production proof.
- `DirectXBackend.read_pixels_with_source()` reports `cpu_mirror` before init
  and may report `swapchain_present` with a positive swapchain handle after an
  initialized D3D/DXVK presentation path. That is presentation provenance, not
  backend device-readback evidence.

Commands when a Windows/DXVK evidence host exists:

```sh
BUILD_DIR=build/production_gui_web_host_gpu_queue_readback_directx \
SIMPLE_BIN=bin/simple \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Focused Windows browser-backing evidence:

```sh
GUI_WEB_2D_DIRECTX_BUILD_DIR=build/gui-web-2d-directx-env \
sh scripts/setup/setup-gui-web-2d-directx-env.shs --browser-backing
```

Acceptance:
- Keep the DirectX wrapper fail-closed until the real D3D/DXVK readback command
  returns `device_readback` with a positive handle and matching checksum.
- Do not mark DirectX production-ready from setup scripts alone.
- Production evidence must include a positive DirectX backend handle with
  same-frame device-readback receipt, not merely `swapchain_present`, or remain
  typed unavailable.
- Browser-backed Windows evidence must record the native DirectX readback gate
  plus Electron and Chrome captures launched with ANGLE D3D11
  (`--use-angle=d3d11`); launch flags alone are not proof without captured ARGB
  and browser proof artifacts.

### WebGPU Agent

Owns WebGPU real-readback preservation and browser/upload provenance
separation.

Current state:
- WebGPU CPU fallback readback is classified as `cpu_mirror`, not
  `device_readback`.
- Initialized WebGPU surfaces may report `surface_upload` with a positive
  `Engine2DReadback.backend_handle`; this is upload provenance, not backend
  device-readback proof.
- `scripts/check/check-webgpu-real-readback.shs` now provides the production
  `webgpu_real` proof: `source=device_readback`, a positive backend handle, and
  matching expected/actual checksum.
- Strict Engine2D WebGPU selection now requires `webgpu_probe_adapter()` to
  report a real GPU adapter. Direct `WebGpuBackend.init()` may keep its
  CPU-mirror path for hermetic rendering tests, but
  `Engine2D.probe_backend("webgpu")` must not report `Initialized` from that
  fallback alone.

Acceptance:
- Keep WebGPU production evidence green only when `webgpu_real` reports
  `device_readback`, positive handle, and checksum match.
- Keep `surface_upload` and CPU mirror paths classified as provenance/fallback,
  never production device proof.

## Platform Spark Tasks + Normal-LLM Verification

These cards are intentionally small enough for Spark agents. A normal LLM should
review the resulting evidence keys before any platform is promoted from
unavailable/provenance-only to production proof.

### Metal Spark Card

- Spark task: run native Metal generated-2D readback on Darwin, then run the
  production wrapper.
- Files: `scripts/check/check-metal-generated-2d-readback.shs`,
  `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`,
  `doc/09_report/production_gui_web_host_gpu_queue_readback_YYYY-MM-DD.md`.
- Command:
  `timeout 240 sh scripts/check/check-metal-generated-2d-readback.shs`.
  Then run the canonical production wrapper with a Metal-capable `bin/simple`.
- Expected evidence keys: `readback_metal_verdict=pass`,
  `metal_spark_task_status=pass`,
  `metal_normal_llm_verification_status=pass`.
- Fail-closed condition: Linux `host-unavailable`, missing `xcrun metal`, or a
  CPU mirror result is not a Metal production pass.
- Safe non-HW guidance: non-macOS agents may update planning text only; keep
  Metal typed unavailable and do not synthesize pass keys without native Darwin
  evidence.
- Normal-LLM verification: confirm the Metal report is from Darwin/native Metal
  tooling and the production report no longer says `host-unavailable`.

### ROCm/HIP Spark Card

- Spark task: run generated-2D readback on an AMD ROCm host, then run the
  production wrapper.
- Files: `scripts/check/check-rocm-generated-2d-readback.shs`,
  `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`,
  `doc/09_report/production_gui_web_host_gpu_queue_readback_YYYY-MM-DD.md`.
- Command:
  `HIP_ARCH=${HIP_ARCH:-gfx1100} timeout 240 sh scripts/check/check-rocm-generated-2d-readback.shs`.
- Expected evidence keys: `readback_rocm_verdict=pass`,
  `rocm_spark_task_status=pass`,
  `rocm_normal_llm_verification_status=pass`.
- Fail-closed condition: missing `hipcc`, loader libraries, device visibility, or
  verified HSACO remains typed unavailable.
- Safe non-HW guidance: agents without an AMD ROCm device may document the lane
  only; do not treat compile-only, probe-only, or unavailable output as a pass.
- Normal-LLM verification: confirm the report proves ROCm/HIP submit/readback on
  a real AMD ROCm stack, not only compilation or probe availability.

### DirectX Spark Card

- Spark task: add or run DirectX readback evidence only after a real D3D/DXVK
  readback command exists.
- Files: `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl`,
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl`,
  `scripts/setup/setup-gui-web-2d-directx-env.shs`, production wrapper/report.
- Command: run the production wrapper on a Windows/DXVK evidence host after the
  DirectX readback command exists.
- Expected evidence keys before real readback:
  `directx_spark_task_status=structured-readback-contract`,
  `directx_normal_llm_verification_status=structured-readback-contract-pass-native-pending`,
  `directx_native_gate_status=unavailable`,
  `presentation_provenance_device_readback_status=not_device_readback`.
- Fail-closed condition: `swapchain_present` is presentation provenance only and
  must not satisfy `device_readback`.
- Safe non-HW guidance: Linux-only agents may keep DirectX as planning/provenance
  work; do not add production pass keys until a Windows/D3D or explicit DXVK
  readback host produces a same-frame device-readback receipt.
- Normal-LLM verification: reject any DirectX promotion unless a same-frame
  `device_readback` receipt and positive DirectX backend handle are present.

### WebGPU Spark Card

- Spark task: expose a WebGPU device readback or explicit GPU readback receipt
  through `Engine2DReadback`.
- Files: `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl`,
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl`,
  production wrapper/report.
- Command: run the production wrapper after WebGPU readback evidence is added.
- Current real-readback evidence keys:
  `webgpu_spark_task_status=pass`,
  `webgpu_normal_llm_verification_status=pass`,
  `presentation_provenance_device_readback_status=not_device_readback`.
- Fail-closed condition: `surface_upload` is upload provenance only and must not
  satisfy `device_readback`.
- Safe non-HW guidance: browserless or adapterless agents may preserve the guard
  state only; do not promote CPU mirror, adapter probe, or upload-handle evidence
  into production queue/readback proof.
- Normal-LLM verification: reject any WebGPU promotion unless the report proves
  same-frame `device_readback` rather than CPU mirror or upload-only evidence.

## Do Not Touch

- Unrelated SSH/crypto/RISC-V work.
- Vendored runtime sources.
- MCP/LSP/package files.
- Other agents' dirty files unless they are explicitly part of this matrix.
