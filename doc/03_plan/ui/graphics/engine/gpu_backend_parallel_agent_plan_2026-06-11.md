# GPU Backend Hardening — Parallel Agent Plan (2026-06-11)

SPipe lane: `.spipe/gpu-backend-dx-harden/state.md`
Model policy: all worker agents run on **Sonnet**; orchestrator integrates,
commits per sub-batch, and pushes to origin/main frequently.

## Host facts (surveyed 2026-06-11)
- nvcc CUDA 13.0 at /usr/local/cuda-13.0/bin/nvcc; nvidia-cuda-toolkit 12.0 (apt)
- Vulkan loader 1.3.275 + ICDs incl. **lavapipe** (libvulkan_lvp.so) → headless
  software Vulkan available for CI-safe real-device tests
- ROCm partial: libhsa-runtime64, libamd-comgr2; **no hipcc**
- Build tools: gcc/g++, cmake, ninja, git, spirv-as; **no meson** (use
  `pip install --user meson`), **no sudo** → local prefix `build/dx/prefix`
- dxvk/dxvk-native/wine/vkd3d **not installed** — source build required

## Architecture context
- Engine2D backend-lane contract: `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`
  (drawing = framebuffer/present/readback; processing = compute kernels/offload)
- DXVK/vkd3d shims exist but leaf is structured-handle only ("pending
  dynamic-loader facade for real libvulkan"): `src/lib/nogc_async_mut/gpu/dxvk_d3d{9,10,11}.spl`,
  `vkd3d_d3d12.spl`, `vulkan_icd_sffi.spl`
- Stack doc to keep current: `doc/04_architecture/ui/simple_gui_stack.md`

## Agent A — CUDA + HIP/ROCm processing backend hardening (Sonnet)
**Exclusive scope** (no other agent touches these):
- `src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl`, `backend_cuda_ext.spl`,
  `backend_cuda_kernels.spl`, `backend_cuda_launch_args.spl`, `sffi_cuda.spl`,
  `cuda_session.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_rocm.spl`, `backend_rocm_kernels.spl`,
  `sffi_rocm.spl`, `rocm_session.spl`
- `src/lib/gc_async_mut/gpu/engine3d/backend_cuda_ext.spl`, `backend_rocm_ext.spl`,
  `sffi_cuda3d.spl`, `sffi_rocm3d.spl`
- Tests: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`
  + new `backend_cuda_processing_spec.spl`, `backend_rocm_processing_spec.spl`
  in the same directory
- Bug doc: `doc/08_tracking/bug/cuda_engine2d_mirror_only_readback_gap_2026-05-29.md`

**Tasks** (in order):
1. Read the mirror-only readback bug doc; close the gap: processing-lane kernel
   dispatch must produce device-side output that lands in the framebuffer
   readback path, not just the host mirror. Verify claims against code (bug-doc
   fixes are author guesses).
2. Probe-driven degradation: no NVIDIA device → structured probe evidence
   ("cuda-device-unavailable"), never silent green.
3. ROCm symmetric wiring; on this host hipcc is missing → probe must report
   `hip-toolchain-missing` as evidence asserted by spec.
4. Specs in interpreter mode (`bin/simple test path`), concrete-value asserts
   only (no `expect(x == y).to_equal(true)`), no skip(), no hollow expects.
5. Update bug doc status + `doc/07_guide/app/ui/engine2d_backend_order.md` if
   ordering/probing semantics changed.

## Agent B — Vulkan processing + Vulkan 2D drawing hardening (Sonnet)
**Exclusive scope**:
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`, `backend_vulkan_glsl.spl`,
  `backend_vulkan_helpers.spl`, `backend_vulkan_session.spl`,
  `backend_vulkan_spirv.spl`, `backend_vulkan_spirv_raster_blobs.spl`,
  `render_2d_vulkan_cross.spl`
- `src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl`, `sffi_vulkan.spl`
- `src/lib/nogc_sync_mut/io/vulkan_sffi.spl`
- Tests: `test/01_unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.spl`,
  `vulkan_icd_sffi_spec.spl` (read-only unless Vulkan-leaf changes require),
  engine2d vulkan specs under `test/01_unit/lib/gc_async_mut/gpu/engine2d/`
  (new `backend_vulkan_processing_spec.spl`, `backend_vulkan_drawing_spec.spl`)
- Bug doc: `doc/08_tracking/bug/engine2d_vulkan_glsl_spirv_parity_2026-05-29.md`

**Tasks**:
1. Fix or root-cause GLSL/SPIR-V parity bug; update bug doc with evidence.
2. Wire headless real-device path via lavapipe (`VK_ICD_FILENAMES` →
   lvp_icd json or loader enumeration); both compute (processing lane) and
   raster (drawing lane) must run and read back deterministic pixels.
3. Harden error paths: device-lost, missing extension, shader compile failure
   → structured errors, not crashes.
4. Specs per SPipe rules (interpreter mode, concrete asserts). Prefer Draw IR
   diff evidence where layout parity is claimed.
5. Keep `doc/04_architecture/ui/simple_gui_stack.md` current if contracts move.

## Agent C — DirectX on Linux + DirectX 2D engine (Sonnet)
**Exclusive scope**:
- `src/lib/nogc_async_mut/gpu/dxvk_d3d9.spl`, `dxvk_d3d10.spl`, `dxvk_d3d11.spl`,
  `vkd3d_d3d12.spl`, `vulkan_icd_sffi.spl`
- NEW: `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl`
  (+ `backend_directx_helpers.spl`, `directx_session.spl` if needed)
- NEW: `scripts/setup/setup-directx-linux.shs`
- `src/os/game/proton/host_readiness.spl` (extend component reporting)
- Tests: `test/01_unit/lib/nogc_async_mut/gpu/*` dxvk/vkd3d specs + NEW
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl`
- Shared-file exception: Agent C is the ONLY agent allowed to edit
  `src/lib/gc_async_mut/gpu/engine2d/mod.spl` / `__init__.spl` for backend
  registration. A and B must NOT touch them.

**Tasks**:
1. `setup-directx-linux.shs`: idempotent local-prefix build into
   `build/dx/prefix` — clone + build wine-vkd3d (autotools/cmake) and
   dxvk-native (meson via `pip install --user meson`, ninja present). No sudo.
   On build failure: record concrete blocker in the lane state file and
   continue with the structured-handle fallback (do not fake success).
2. Wire the real dynamic-loader facade leaf in vulkan_icd_sffi/dxvk/vkd3d shims: when
   prefix libs (or system libvulkan for the ICD leaf) exist, route through
   them; otherwise keep structured handles. Dispatch-chain specs must assert
   WHICH leaf ran (evidence string `leaf=dlopen` vs `leaf=structured`).
3. Implement `backend_directx` Engine2D drawing backend: D3D11 device/swapchain
   semantics over dxvk_d3d11 on Linux; on Windows route to native d3d11
   behind a platform probe. Primitive draw + clear + readback parity with
   backend_cpu output for a small fixture scene.
4. Specs runnable on BOTH platforms: platform probe selects expected evidence;
   no skip(); Windows-only branches assert probe evidence on Linux.
5. Update `doc/07_guide/app/ui/engine2d_backend_order.md` + stack doc with the
   new backend; record DirectX setup guide under `doc/07_guide/ui/`.

## Agent D — GUI rendering path watcher (Sonnet)
**Exclusive scope** (everything rendering-path NOT owned by A/B/C):
- `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`, `backend_cpu.spl`,
  `compositor.spl`, draw_ir files in engine2d, `helpers_*.spl`,
  `framebuffer_surface.spl`, `web_render_session.spl`
- `src/lib/common/ui/draw_ir.spl`, `window_scene_draw_ir.spl` (fix-only)
- Browser renderer specs under `test/01_unit/lib/gc_async_mut/gpu/browser_engine/`

**Tasks** (loop until other lanes land):
1. Run the engine2d + browser_engine + web renderer spec lanes in interpreter
   mode; triage failures.
2. Fix root-cause regressions inside its scope; for failures owned by A/B/C
   scopes, file/append a concrete bug doc instead of editing their files.
3. Re-run after each fix; commit per lint-clean sub-batch.
4. Final pass: re-run full rendering lanes after A/B/C commits land; report
   residual red with bug docs.

## Shared-file & VCS protocol (all agents)
- Shared files (`mod.spl`, `__init__.spl`, `backend.spl`, `backend_probe.spl`,
  `backend_session.spl`, `engine2d_api.spl`, `sffi_dispatch.spl`): only Agent C
  may edit `mod.spl`/`__init__.spl`; everyone else reports needed shared edits
  in `.spipe/gpu-backend-dx-harden/state.md` under "## Shared Edits Requested"
  for the orchestrator to apply.
- Commit with `jj commit -m "<lane>: msg"` immediately after each lint-clean
  sub-batch (Edit-tool changes are NOT snapshotted until a jj command runs;
  parallel reconciles can clobber uncommitted edits).
- Never create branches. Orchestrator pushes (`sj bookmark set main -r @- &&
  sj git push --bookmark main`) after each integration round and verifies
  content with `git log -S`.
- No skip(), no TODO→NOTE, no boolean-wrapper asserts, fix .spl not Rust.
