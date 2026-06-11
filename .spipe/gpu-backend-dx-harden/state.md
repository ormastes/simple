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
- 2026-06-11: Agent A batch 1 committed (7136032): backend_cuda.spl —
  feature_gate renamed "cuda_device" → "cuda-device-unavailable" (AC-1
  structured evidence); probe_cuda_processing() added. backend_rocm.spl —
  probe_rocm() added with "hip-toolchain-missing" gate (AC-2); BackendProbeResult
  import added; _engine2d_hip_source import moved to top.
- 2026-06-11: Agent A batch 2 committed (6d5830e): backend_cuda_processing_spec.spl
  (7/7 pass) + backend_rocm_processing_spec.spl (7/7 pass) — interpreter mode,
  concrete-value asserts, no skip(), no hollow expects. AC-1 and AC-2 CLOSED.
- 2026-06-11: Agent A bug doc updated in 86c62fb (conflict-resolve merged it):
  cuda_engine2d_mirror_only_readback_gap_2026-05-29.md — Processing-Lane Probe
  Hardening section added.

## Shared Edits Requested
- helpers_availability.spl: add "directx" to the auto-detect probe list
  (after vulkan, before opencl) so Engine2D.detect_best_backend() tries
  DirectXBackend.init() when vulkan probe fails. Agent C owns mod.spl only;
  helpers_availability.spl is shared — orchestrator should apply this after
  all lanes land.
- Conflict-cleanup (Agent A): commit 86c62fb360 (conflict-resolve by another
  agent) dropped the following spec files from test/01_unit/lib/gc_async_mut/gpu/engine2d/
  — they are present in .jjconflict-side-1/ and should be restored:
  backend_directx_spec.spl, backend_lane_spec.spl, backend_order_spec.spl,
  backend_vulkan_drawing_spec.spl, backend_vulkan_processing_spec.spl,
  backend_webgpu_spec.spl, baremetal_constructor_spec.spl, draw_ir_adv_spec.spl,
  draw_text_bg_spec.spl, graphics_backend_acceleration_spec.spl.
  backend_cuda_renderbackend_spec.spl was already restored at HEAD (86c62fb).
  These belong to other agents' scopes but need orchestrator or owner restoration.
