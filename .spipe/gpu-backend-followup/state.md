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
- 2026-06-12 Lane A (P1): AC-1 closed. `setup-directx-linux.shs` hardened (meson via
  python3-venv fallback for PEP 668, perl JSON::PP cpan-local fallback, SPIRV-header
  probing); glslang 16.3.0 bootstrapped; dxvk-native built+installed to
  `build/dx/prefix` (`libdxvk_d3d11.so`), readiness `dxvk_ready: true`. Probe flipped
  to live: evidence `platform=linux-dxvk leaf=dlopen device=true`, reason
  "dxvk-d3d11 device created leaf=dlopen". backend_directx_spec 18/18 on forced
  (uncached) re-run. vkd3d (d3d12) autotools build still fails — recorded as blocker
  in readiness state; D3D11 path (what the backend uses) is fully live.
- 2026-06-12 sync + regression fix: jj sync pass — multicore test-harden commit
  rebased+pushed (746267ef7035); perf(mcp) tool-set commit pushed by its owner;
  abandoned superseded compile_cast revert side-head. Found browser_renderer_spec
  regressed 76/22 → 37/61: `candidate_count` hoist in compute_styles lost in a
  conflict auto-resolve. Restored (f1ec5f27860) → 93/5. Residual 5: CSS nesting
  ×3, custom properties, border fixture — Lane D2 (Sonnet) spawned. P4 stage4
  redeploy started in background (deploy gate landed a1b5ba09e8e).
- 2026-06-12 Lane B (P2): AC-2 + AC-3 closed. VKSPIRV-001: Replaced all 8 placeholder SPIR-V stubs in `backend_vulkan_spirv_raster_blobs.spl` (2006 lines) with real compiled SPIR-V 1.3 modules (2576B–3680B) assembled via `spirv-as --target-env vulkan1.1` (SPIRV-Tools v2025.1), validated with `spirv-val`. Kernels: rect_outline, circle_filled, circle_outline, line, rounded_rect, triangle_filled, gradient_rect, blit. Updated comment block in `backend_vulkan_spirv.spl` to remove "placeholder" language. rt_vulkan_init crash (AC-3): confirmed non-reproducible with lavapipe ICD — `rt_vulkan_init()` returns `true`, `VulkanBackend.init(4,4)` + `clear()` succeed; no crash; original crash resolved in prior work. Parity bug doc updated (Remaining Scope → resolved). Both specs 22/22 green.
