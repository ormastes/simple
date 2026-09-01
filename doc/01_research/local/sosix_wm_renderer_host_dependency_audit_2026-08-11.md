# SOSIX WM/renderer host dependency audit — 2026-08-11

## Migrated in this slice

`compositor_engine2d.spl` no longer selects its backend by reading
`SIMPLE_GUI_BACKEND` itself. The environment read is owned by
`os.sosix.host.configuration_adapter`; portable selection and the new
`create_from_host_configuration` path consume `SosixHostConfigurationSnapshot`.
The compatibility `create_from_env` entrypoint delegates through that adapter.
DrawIr composition, Engine2D execution, and Engine3D remain unchanged.

The follow-up slice also captures the four Engine2D transfer settings in that
snapshot. Revision-cache eligibility now compares a compositor-owned immutable
profile and performs no environment reads during rendering. The legacy
constructor still samples the same variables once through the host adapter.

The boot screen factory follow-up removes its direct runtime declaration.
`screen_type_from_configured_or` is now the pure configuration ingress for
SOSIX/guest-owned values, while the compatibility environment entrypoint uses
the standard environment facade and delegates immediately to that pure core.

## Remaining direct-runtime inventory

- Compositor policy/configuration: startup configuration in
  `host_compositor_bootstrap.spl` and `host_compositor_core.spl`.
- Presentation/input platform adapters: Cocoa, SDL2, Win32, winit, UART and
  hosted-input modules still declare their platform runtime functions. These
  are legitimate adapter owners, but their callers still need complete SOSIX
  request/completion routing.
- Timing/evidence/storage: `frame_pacer.spl`, capture/evidence modules,
  `pixel_content_store.spl`, and hosted browser worker/registry/session modules
  retain clock, file, environment, or process runtime calls.
- Engine2D device adapters: CUDA, Metal, Vulkan, WebGPU, OpenCL, ROCm, CPU SIMD,
  framebuffer hooks, and host GPU queues retain device/runtime calls. These
  belong below Engine2D but are not yet represented uniformly as SOSIX
  capability-backed submissions.
- Browser renderer support: timer API, resource/file loaders, byte conversion,
  randomness, and HTTP/WebSocket transports retain direct runtime calls.
- Engine3D math/device dispatch is already separated from compositor DrawIr;
  it should remain a distinct migration lane rather than being routed through
  the WM/Engine2D capability.

## Recommended next bounded migrations

1. Convert browser script timers to the existing SOSIX timer request/completion
   contract.
2. Route compositor evidence storage through registered SOSIX filesystem
   buffers without changing frame ownership.
