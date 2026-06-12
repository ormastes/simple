# gpu-backend-followup — SPipe Dev State

## Task Type
Execution of follow-up plan
`doc/03_plan/ui/graphics/backends/gpu_backend_dx_harden_followup_plan.md`
(remainder of gpu-backend-dx-harden).

## Acceptance Criteria
- AC-1 (P1): dxvk/vkd3d prefix built via `scripts/setup/setup-directx-linux.shs`;
  backend_directx probe flips to live evidence; spec green against real ICD.
- AC-2 (P2a): VKSPIRV-001 — placeholder SPIR-V blobs replaced with real
  compiled SPIR-V; processing-lane kernels verified.
- AC-3 (P2b): rt_vulkan_init interpreter crash root-caused; lavapipe e2e
  readback test runs (or concrete blocker documented in parity bug doc).
- AC-4 (P5): browser_renderer_spec residual 22 failures fixed at root cause
  (`:has(> )` depth-blind normalize_child_combinators + cross-test state).
- AC-5 (P6): CUDA mirror-only readback gap closed; readback matches lane
  contract.
- AC-6 (P4, post-lanes): stage4 redeploy picks up interpreter fix in run-mode;
  deploy-gate refuses swap without probed seed.
- AC-7: per-batch jj commits; orchestrator integrates + pushes to origin/main.

## Lane Ownership (parallel agents — disjoint file scopes)
- A (P1): `scripts/setup/setup-directx-linux.shs`,
  `test/.../engine2d/backend_directx_spec.spl`, dx prefix dir
- B (P2): `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan*`,
  `vulkan_icd_sffi*`, `src/runtime/` rt_vulkan_* externs,
  `test/.../engine2d/backend_vulkan*`, parity bug doc
- D (P5): browser renderer selector/normalize code + renderer specs,
  browser_renderer bug doc
- E (P6): `backend_cuda*`, rt_cuda_* readback externs,
  `test/.../engine2d/backend_cuda*`, cuda readback bug doc
- Orchestrator: P4 after lanes land; integration pushes

## Log
- 2026-06-12: state created; lanes A/B/D/E spawned (Sonnet, background).
- 2026-06-12 Lane E (P6): AC-5 closed. Added `fn is_usable()` to `BackendProbeResult` in `backend_probe.spl`; added `use std.gpu.engine2d.backend_cuda_ext` to renderbackend spec. Device→host readback (`cuda_memcpy_dtoh`) was already correct; gap was spec compilation failures. renderbackend spec: 9p/2f → 11p/0f; processing spec: 7p/0f unchanged. No new externs; no seed rebuild needed.
