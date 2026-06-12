# GPU Backend / DirectX Harden — Follow-up Plan

**Date:** 2026-06-12
**Predecessor:** `.spipe/gpu-backend-dx-harden/state.md` (ACs 1–3, 5–7, 9 closed;
AC-4 partial; AC-3/AC-8 closed with recorded follow-ups)
**Status of original goal:** ~90% complete. This plan covers the remainder.

## Completed (for context)

- CUDA/HIP + Vulkan processing backends hardened; drawing/processing lane
  contract in `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`.
- DirectX backend implemented and registered (`backend_directx.spl`,
  `engine.spl` strict-create + probe arms, `helpers_availability.spl`
  priority 5, order spec 13 entries) — Linux specs 18/18 in interpreter mode.
- Vulkan 2D engine hardened: `VulkanErrorKind` + classify, initialized guards
  on 12 draw/present methods, headless (lavapipe) device selection,
  `fn read_pixels()` purity fix; specs 22/22 + 22/22.
- Interpreter root-cause fix shipped (964a30ebe86): typed/tuple `val` bindings
  in nested closure blocks bound nothing (`exec_block_closure_mut`).

## Remaining Work

### P1 — DirectX runtime prefix build (closes AC-4)
The setup script and readiness probe shipped (0bf1773151) but the dxvk/vkd3d
prefix build was deferred because the agent sandbox had no network.
- [x] Run `sh scripts/setup/setup-directx-linux.shs` with network access.
      (2026-06-12: dxvk-native built into `build/dx/prefix`, `dxvk_ready: true`;
      vkd3d/d3d12 autotools build fails — recorded blocker, D3D11 path unaffected.)
- [x] Re-run `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl`
      against the real DXVK ICD (probe should flip from gated to live).
      (18/18 on forced re-run.)
- Verified: probe evidence `platform=linux-dxvk leaf=dlopen device=true`,
  reason "dxvk-d3d11 device created leaf=dlopen".

### P2 — Vulkan follow-ups from AC-3 (bug doc: `doc/08_tracking/bug/engine2d_vulkan_glsl_spirv_parity_2026-05-29.md`)
- [x] VKSPIRV-001: replace placeholder SPIR-V blobs with real compiled SPIR-V
      for the processing kernels (GLSL → SPIR-V parity).
      (2026-06-12: all 8 blobs real SPIR-V 1.3, spirv-as + spirv-val; pushed
      7875a3e7d5f.)
- [x] Root-cause the `rt_vulkan_init` interpreter crash that blocks the full
      lavapipe end-to-end readback test. (Non-reproducible — returns true with
      lavapipe; init+clear succeed; resolved by prior interpreter fix.)

### P3 — Windows-side validation (AC-6 was probe-gated)
- [ ] Run the DirectX 2D engine specs on a real Windows host (native D3D11);
      Linux side already green via DXVK path.

### P4 — Stage4 redeploy + deploy-gate hardening
- [ ] Redeploy stage4 so `bin/simple run` picks up the nested-closure
      typed-binding fix (currently only `test` mode, via the rebuilt seed,
      has it). After redeploy, optionally restore the annotated
      `val NAME: u32 = 0x...` forms in the Vulkan specs.
- [ ] Deploy-gate: refuse the stage4 binary swap unless a probed seed exists
      at the delegate path (suggested in
      `doc/08_tracking/bug/stage4_deploy_no_seed_test_runner_blocked_2026-06-11.md`).

### P5 — GUI rendering path residual (Agent D lane, AC-8)
Bug doc: `doc/08_tracking/bug/browser_renderer_spec_sequence_failures_2026-06-11.md`
- [ ] Fix depth-blind `normalize_child_combinators` for `:has(> ...)`.
- [ ] Isolate cross-test renderer state; clear the residual 22 failures in
      `browser_renderer_spec` (76 pass / 22 fail as of 2026-06-11).

### P6 — CUDA readback gap (pre-existing, same subsystem)
Bug doc: `doc/08_tracking/bug/cuda_engine2d_mirror_only_readback_gap_2026-05-29.md`
- [x] Close the mirror-only readback gap so CUDA drawing-lane readback matches
      the Vulkan/CPU contract. (2026-06-12: `cuda_memcpy_dtoh` readback was
      already correct; gap was spec compile failures — fixed, 11/0 + 7/0;
      pushed dfcc7fd6bcf.)

## Verification

```bash
bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/   # all backend specs
sh scripts/setup/setup-directx-linux.shs                       # P1 prefix build
bin/simple build bootstrap                                     # before P4 redeploy
```

## Suggested Lane Split (if run as parallel agents)

| Lane | Scope (disjoint) | Items |
|------|------------------|-------|
| A | `scripts/setup/`, `backend_directx*` | P1, P3 prep |
| B | `backend_vulkan*`, `vulkan_icd_sffi`, runtime vulkan externs | P2 |
| C | compiler/bootstrap scripts, deploy gate | P4 |
| D | browser renderer (`src/app/browser*`, renderer specs) | P5 |
| E | `backend_cuda*` + cuda runtime externs | P6 |
