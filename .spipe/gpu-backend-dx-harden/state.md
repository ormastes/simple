# gpu-backend-dx-harden — SPipe Dev State

## Task Type
feature (hardening + new backend)

## Refined Goal
Fully harden the Engine2D GPU **processing** backends (CUDA, HIP/ROCm, Vulkan
compute) and the Vulkan 2D **drawing** engine; set up DirectX on this Linux
host (local-prefix vkd3d/dxvk-native build, no sudo) and implement a DirectX
2D engine backend with tests runnable on both Linux (via DXVK/vkd3d→Vulkan)
and Windows (native D3D11); keep the GUI rendering path green in parallel.
Sync GitHub frequently (commit per sub-batch, push often).

## Acceptance Criteria
- AC-1: CUDA processing backend closes the mirror-only readback gap
  (doc/08_tracking/bug/cuda_engine2d_mirror_only_readback_gap_2026-05-29.md):
  device-side kernel dispatch produces framebuffer-affecting output verified by
  readback evidence in an interpreter-mode spec; graceful probe fallback when
  no NVIDIA device.
- AC-2: HIP/ROCm processing backend has real-dispatch wiring symmetric with
  CUDA, with a probe that reports `hipcc missing` / no-device as structured
  evidence (not silent pass) on this host.
- AC-3: Vulkan processing (compute) lane and Vulkan 2D drawing lane both run
  against a real Vulkan device using the lavapipe software ICD
  (libvulkan_lvp.so) headlessly; GLSL/SPIR-V parity bug
  (engine2d_vulkan_glsl_spirv_parity_2026-05-29.md) fixed or root-caused with
  updated bug doc.
- AC-4: `scripts/setup/setup-directx-linux.shs` builds/installs vkd3d (and
  dxvk-native when buildable) into a local prefix (build/dx/prefix) without
  sudo, idempotent, and records component readiness via
  src/os/game/proton/host_readiness.spl conventions.
- AC-5: New `backend_directx` Engine2D drawing backend exists in
  src/lib/gc_async_mut/gpu/engine2d/, delegating D3D11→DXVK→Vulkan on Linux
  and native d3d11 on Windows behind a platform probe; registered in the
  backend order docs.
- AC-6: DirectX 2D engine unit specs pass in interpreter mode on Linux and are
  structured to run on Windows (platform probe drives expected evidence
  strings; no skip(), no hollow expects, no boolean-wrapper asserts).
- AC-7: dxvk_d3d9/10/11 + vkd3d_d3d12 shims gain a real `rt_dlopen` leaf path
  (used when the local prefix libs exist) while keeping the structured-handle
  path as fallback; dispatch-chain specs updated to assert which leaf ran.
- AC-8: GUI rendering path stays green: engine2d/web-renderer spec lanes run
  by the watcher agent; any regression found is fixed or filed as a concrete
  bug doc under doc/08_tracking/bug/.
- AC-9: Work is committed in small lane-scoped jj commits and pushed to
  origin/main repeatedly during the session (not one final push).

## Lane Ownership (parallel agents — disjoint file scopes)
See doc/03_plan/ui/graphics/engine/gpu_backend_parallel_agent_plan_2026-06-11.md

## Log
- 2026-06-11: lane created; host survey done (nvcc 13.0 present, lavapipe
  present, no hipcc, no sudo, no meson — pip --user fallback; dxvk/vkd3d shims
  are structured-handle, leaf dlopen pending).
- 2026-06-11: Agent C batch 1 committed (5fb): setup-directx-linux.shs,
  vulkan_icd_sffi.spl dlopen leaf + VkIcdResult.leaf field,
  host_readiness.spl DxPrefixReadiness + dx_prefix_probe().
- 2026-06-11: Agent C batch 2 in progress: backend_directx.spl,
  backend_directx_spec.spl, mod.spl registration, engine2d_backend_order.md
  updated (directx inserted after vulkan), setup guide written.

## Shared Edits Requested
- helpers_availability.spl: add "directx" to the auto-detect probe list
  (after vulkan, before opencl) so Engine2D.detect_best_backend() tries
  DirectXBackend.init() when vulkan probe fails. Agent C owns mod.spl only;
  helpers_availability.spl is shared — orchestrator should apply this after
  all lanes land.
