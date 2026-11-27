# Simple 2D / Simple web test coverage — measured 2026-11-14

Owner target (2026-11-13): 90% or more line and branch coverage. This file
records what is measurable on this host today, the measured numbers, and the
distance to 90%. Source tree: `21e2012095d` + the test-only commits of
`work/render-coverage-20261114`.

Scopes

- Simple 2D: `src/lib/gc_async_mut/gpu/engine2d/**`, `src/lib/nogc_sync_mut/gpu/engine2d/**`,
  `src/lib/common/gpu/engine2d/**` (165 files).
- Simple web: `src/lib/gc_async_mut/gpu/browser_engine/**` (181 files).

## Method that works here

Binary: Rust seed `~/.cache/cargo-target-webrender-vk/release/simple`
(sha256 `08aba9746a813ee7…`, built 2026-11-14 09:32), interpreter lane.

```bash
# 1. one artifact per spec (line, function, decision and condition rows)
SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<spec>.sdn \
  systemd-run --user --scope -q -p MemoryMax=8G timeout 900 $S run <spec.spl>
# 2. union the artifacts (hit counts summed per file/line and per decision id)
# 3. score one module with the repo's own scorer
$S spl-coverage module --file <merged.sdn> src/lib/.../<module>.spl
#   -> coverage-module: <path> lines=..% (hit/exec) decisions=..% (both outcomes) outcomes=..% conditions=..%
```

`spl-coverage module` (`src/app/spl_coverage/main.spl`,
`src/lib/common/coverage_module_report.spl`) owns the denominator: executable
lines found by scanning the source, and a line counts as hit only when its
enclosing function also has a call count. It refuses an artifact recorded
against a different source version (crc32), so every number below is
`source=verified`.

Calibration on a hand-countable fixture (3 functions, one never called, one
`if` taken one way, one `while`): `lines=77.7% (7/9) decisions=50.0% (1/2)
outcomes=75.0% (3/4)` — the uncalled function's two lines are the misses and
the one-sided `if` is the missing decision, as expected. The scanner's
denominator was not audited line by line beyond this fixture.

What does NOT work on this host

| lane | result |
|---|---|
| `simple test <spec> --coverage` | `ERROR: --coverage needs a directory target` |
| `simple test <dir> --coverage` (instrumented build) | 9 min on a 2-example fixture, then `MC/DC: DEGRADED … coverage-abort: wrapper compile timeout`, empty artifact |
| `SIMPLE_COVERAGE=1 simple test <spec>` | `spawned test process did not publish a valid child APK activation receipt`, rc=1 |
| `spl-coverage rollup --file a --file b` on full artifacts | not used: full artifacts are 1.6–4 MB each; the union was done by a 60-line script that sums the same rows |

Coverage kinds obtainable today: **line** and **decision / outcome** (branch)
per module: yes. **Condition** rows exist but are sparse. **MC/DC: no** — the
seed prints `MC/DC: unavailable (compiler lacks probe emission)`; it needs the
self-hosted binary. JIT/native execution is not measured at all (interpreter
only), and GPU-side execution is invisible to any of this.

Limits of the numbers

- 862 specs were selected (the three owning spec directories plus every spec
  that imports `gpu.engine2d` / `gpu.browser_engine`). **771 were swept, 91
  were not** (the tail of `test/03_system`, `test/05_perf`, `test/feature`,
  `test/system`): the sweep is serial under a shared host and was frozen after
  about three hours. Totals are therefore a lower bound for those 91.
- 506 runs exited 0, 261 exited 1, 3 crashed (139), 1 timed out. Lines executed
  by a spec that later fails an assertion ARE counted — this is execution
  coverage, not "covered by a passing assertion".
- 18 specs executed zero examples on this seed. The two
  `BaremetalBackend` specs fail the same way under plain `simple test`
  (`cannot resolve import os.drivers.framebuffer.fb_driver`), which is why
  `backend_baremetal.spl` reads 0/337.
- Functions that only return a literal (the 18 embedded SPIR-V blobs, kernel
  source strings) have zero executable lines for this scorer, so a spec over
  them adds no measured coverage however useful it is.
- `@cover <path> <pct>%` headers are not a coverage measurement; they are an
  admission annotation. The 16 specs added in this branch carry the value
  measured for that spec alone with the command above.

## Distance to 90% (after)

Simple 2D — 8,518 executable lines uncovered, 6,548 more hits needed:

| bucket | uncovered lines |
|---|---:|
| non-Vulkan host backends (metal, opencl, rocm, cuda, directx, intel, webgpu, baremetal, sffi/ffi shims) | 4,334 |
| Vulkan backend files | 1,828 |
| everything else (engine, draw IR, software/emu rasterizer, queues) | 2,356 |

Covering every line outside the non-Vulkan backends would reach about 78%.
**90% for Simple 2D is not reachable on a Linux host without either running
the Metal/OpenCL/ROCm/CUDA/DirectX backends or an owner decision to scope them
out of the denominator** (`spl-coverage module --os/--arch` only excludes
`@when` bodies, which these files do not use).

Simple web — 8,749 uncovered, 4,858 more hits needed; 7,514 of them are in
host-independent code, so 90% is reachable with CPU specs.

Next, in order of executable-line deficit:

1. Simple web: `webgl_context.spl` (590), `webgpu_commands.spl` (350 after this
   branch: the `*_with_resources` validators and render-pass descriptor),
   `webgpu_context.spl` (379), `js/parser.spl` + `js/interpreter.spl` (618,
   never loaded by any swept spec), `style_rule_index.spl` (344),
   `dom_accessors.spl` (338, child insert/remove), `simple_web_fractional_box_resolver.spl`
   (300, never loaded), `simple_web_html_layout_renderer_foundation.spl` (231).
2. Simple 2D reachable: `engine.spl` (485), `draw_ir_adv.spl` (311),
   `backend_emu.spl` / `backend_software.spl` remaining primitives (arc,
   rounded-rect outline, gradient stops, blur/shadow, image transform),
   `backend_baremetal.spl` (337 — first fix the `os.drivers` import of its specs),
   `host_gpu_event_queue.spl` typed dispatch paths.
3. Simple 2D Vulkan (1,828): needs the real-GPU lane with coverage enabled, or
   CPU specs of the pure planning helpers in `backend_vulkan_helpers.spl` /
   `backend_vulkan_font.spl`.
4. Sweep the 91 unswept system specs, and finish the 18 zero-example specs.
5. Decision coverage (36% / 55%) is far below line coverage in both scopes;
   every new spec should take both sides of each guard, not just the happy path.


## Totals

| scope | files | never loaded by any spec | line % before | line % after | lines hit/exec after | decision (both outcomes) % before | after | outcome % after | lines still missing for 90% |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Simple 2D | 165 | 57 | 56.6 | 56.8 | 11188/19706 | 35.8 | 36.4 | 51.2 | 6548 |
| Simple web | 181 | 34 | 75.5 | 77.5 | 30162/38911 | 53.4 | 54.9 | 71.2 | 4858 |

## Simple 2D per file (sorted by uncovered executable lines, after)

`loaded=no` means no spec in the sweep imported the module at all.

| file (under src/lib/) | exec lines | hit before | hit after | line % after | decisions | both-outcome % | outcome % | loaded |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| gc_async_mut/gpu/engine2d/backend_metal.spl | 1303 | 66 | 66 | 5.1 | 391 | 2.3 | 5.5 | yes |
| gc_async_mut/gpu/engine2d/engine.spl | 1321 | 836 | 836 | 63.3 | 521 | 35.1 | 59.6 | yes |
| gc_async_mut/gpu/engine2d/backend_vulkan.spl | 1501 | 1034 | 1034 | 68.9 | 501 | 30.7 | 51.1 | yes |
| gc_async_mut/gpu/engine2d/backend_opencl.spl | 491 | 72 | 72 | 14.7 | 119 | 1.7 | 15.1 | yes |
| gc_async_mut/gpu/engine2d/opencl_session.spl | 468 | 120 | 120 | 25.6 | 213 | 8.9 | 18.1 | yes |
| gc_async_mut/gpu/engine2d/backend_rocm.spl | 417 | 72 | 72 | 17.3 | 105 | 0.0 | 10.0 | yes |
| gc_async_mut/gpu/engine2d/backend_baremetal.spl | 337 | 0 | 0 | 0.0 | 88 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl | 1075 | 739 | 739 | 68.7 | 291 | 24.4 | 44.3 | yes |
| gc_async_mut/gpu/engine2d/backend_vulkan_font.spl | 945 | 615 | 615 | 65.1 | 282 | 40.4 | 54.6 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_adv.spl | 1765 | 1454 | 1454 | 82.4 | 539 | 62.0 | 77.2 | yes |
| gc_async_mut/gpu/engine2d/backend_virtio_gpu.spl | 273 | 0 | 0 | 0.0 | 71 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/vulkan_resident_2d.spl | 299 | 66 | 66 | 22.1 | 87 | 12.6 | 15.5 | yes |
| gc_async_mut/gpu/engine2d/backend_cuda.spl | 566 | 357 | 357 | 63.1 | 177 | 20.9 | 48.6 | yes |
| nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl | 342 | 137 | 137 | 40.1 | 129 | 6.2 | 29.8 | yes |
| gc_async_mut/gpu/engine2d/backend_metal_font.spl | 278 | 91 | 91 | 32.7 | 90 | 11.1 | 17.2 | yes |
| gc_async_mut/gpu/engine2d/backend_intel.spl | 178 | 22 | 22 | 12.4 | 31 | 0.0 | 9.7 | yes |
| gc_async_mut/gpu/engine2d/backend_metal_helpers.spl | 126 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_software.spl | 1141 | 1020 | 1020 | 89.4 | 309 | 66.7 | 80.7 | yes |
| gc_async_mut/gpu/engine2d/metal_session.spl | 138 | 18 | 18 | 13.0 | 48 | 14.6 | 17.7 | yes |
| gc_async_mut/gpu/engine2d/render_2d_riscv.spl | 91 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| nogc_sync_mut/gpu/engine2d/sffi_cuda.spl | 71 | 0 | 0 | 0.0 | 27 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/render_2d_x86_session.spl | 70 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/rocm_session.spl | 114 | 46 | 46 | 40.4 | 42 | 4.8 | 22.6 | yes |
| gc_async_mut/gpu/engine2d/final_output_capture.spl | 66 | 0 | 0 | 0.0 | 20 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/cuda_session.spl | 147 | 87 | 87 | 59.2 | 59 | 20.3 | 43.2 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_target_metal.spl | 58 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_directx.spl | 159 | 105 | 105 | 66.0 | 45 | 22.2 | 50.0 | yes |
| gc_async_mut/gpu/engine2d/vulkan_session.spl | 224 | 170 | 170 | 75.9 | 82 | 47.6 | 61.6 | yes |
| gc_async_mut/gpu/engine2d/backend_opengl.spl | 69 | 16 | 16 | 23.2 | 11 | 0.0 | 18.2 | yes |
| gc_async_mut/gpu/engine2d/host_gpu_event_queue.spl | 118 | 61 | 65 | 55.1 | 59 | 28.8 | 50.0 | yes |
| gc_async_mut/gpu/engine2d/backend_vulkan_session.spl | 55 | 6 | 6 | 10.9 | 18 | 0.0 | 8.3 | yes |
| gc_async_mut/gpu/engine2d/cpu_session.spl | 48 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_cuda_proof.spl | 46 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_webgpu.spl | 229 | 183 | 183 | 79.9 | 77 | 48.1 | 68.8 | yes |
| gc_async_mut/gpu/engine2d/corpus_case02_capture_artifact.spl | 45 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/corpus_case06_capture_artifact.spl | 43 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_cuda_ext.spl | 43 | 3 | 3 | 7.0 | 21 | 0.0 | 4.8 | yes |
| gc_async_mut/gpu/engine2d/backend_lane.spl | 68 | 28 | 28 | 41.2 | 27 | 14.8 | 31.5 | yes |
| nogc_sync_mut/gpu/engine2d/sffi_directx.spl | 48 | 8 | 8 | 16.7 | 17 | 0.0 | 11.8 | yes |
| nogc_sync_mut/gpu/engine2d/arm_riscv_session.spl | 38 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/render_2d_vulkan_cross.spl | 37 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| nogc_sync_mut/gpu/engine2d/ffi_cuda.spl | 54 | 17 | 17 | 31.5 | 20 | 0.0 | 15.0 | yes |
| nogc_sync_mut/gpu/engine2d/ffi_intel.spl | 32 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| nogc_sync_mut/gpu/engine2d/sffi_intel.spl | 34 | 3 | 3 | 8.8 | 12 | 0.0 | 4.2 | yes |
| gc_async_mut/gpu/engine2d/backend_vulkan_font_types.spl | 30 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/vulkan_async_submission.spl | 54 | 24 | 24 | 44.4 | 23 | 13.0 | 41.3 | yes |
| gc_async_mut/gpu/engine2d/wm_frame_pacing.spl | 30 | 0 | 0 | 0.0 | 5 | 0.0 | 0.0 | yes |
| nogc_sync_mut/gpu/engine2d/ffi_rocm.spl | 30 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_emu.spl | 662 | 633 | 633 | 95.6 | 190 | 71.6 | 85.8 | yes |
| gc_async_mut/gpu/engine2d/glyph.spl | 78 | 50 | 50 | 64.1 | 25 | 36.0 | 54.0 | yes |
| gc_async_mut/gpu/engine2d/helpers_availability.spl | 148 | 120 | 120 | 81.1 | 73 | 67.1 | 78.8 | yes |
| nogc_sync_mut/gpu/engine2d/cpu_simd_session.spl | 49 | 21 | 21 | 42.9 | 18 | 0.0 | 22.2 | yes |
| gc_async_mut/gpu/engine2d/ffi_dispatch.spl | 27 | 0 | 0 | 0.0 | 10 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/sffi_dispatch.spl | 27 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| nogc_sync_mut/gpu/engine2d/sffi_rocm.spl | 29 | 2 | 2 | 6.9 | 7 | 0.0 | 0.0 | yes |
| nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl | 44 | 18 | 18 | 40.9 | 5 | 0.0 | 30.0 | yes |
| gc_async_mut/gpu/engine2d/backend_webgpu_proof.spl | 33 | 8 | 8 | 24.2 | 12 | 0.0 | 20.8 | yes |
| gc_async_mut/gpu/engine2d/corpus_case01_capture_artifact.spl | 23 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/compositor.spl | 71 | 49 | 49 | 69.0 | 19 | 31.6 | 55.3 | yes |
| gc_async_mut/gpu/engine2d/gui_button_capture_artifact.spl | 22 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| nogc_sync_mut/gpu/engine2d/simd_kernels.spl | 228 | 206 | 206 | 90.4 | 73 | 61.6 | 78.1 | yes |
| gc_async_mut/gpu/engine2d/backend_webgpu_proof_runtime_ops.spl | 23 | 2 | 2 | 8.7 | 12 | 0.0 | 4.2 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_box_effects.spl | 295 | 265 | 274 | 92.9 | 100 | 72.0 | 85.5 | yes |
| gc_async_mut/gpu/engine2d/physical_capture_artifact.spl | 21 | 0 | 0 | 0.0 | 9 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/web_opaque_box_capture_artifact.spl | 21 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_rocm_kernels.spl | 20 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_session.spl | 20 | 0 | 0 | 0.0 | 10 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl | 242 | 222 | 222 | 91.7 | 118 | 77.1 | 88.6 | yes |
| nogc_sync_mut/gpu/engine2d/vulkan_session.spl | 52 | 33 | 33 | 63.5 | 18 | 50.0 | 50.0 | yes |
| common/gpu/engine2d/directx_submission_receipt.spl | 26 | 9 | 9 | 34.6 | 12 | 33.3 | 37.5 | yes |
| gc_async_mut/gpu/engine2d/backend.spl | 21 | 5 | 5 | 23.8 | 7 | 0.0 | 0.0 | yes |
| nogc_sync_mut/gpu/engine2d/simd_isa_provider.spl | 111 | 95 | 95 | 85.6 | 35 | 54.3 | 72.9 | yes |
| gc_async_mut/gpu/engine2d/environment_resident_executor_v1.spl | 133 | 118 | 118 | 88.7 | 28 | 67.9 | 83.9 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_packed_composition_owner_v3.spl | 79 | 65 | 65 | 82.3 | 17 | 64.7 | 79.4 | yes |
| gc_async_mut/gpu/engine2d/helpers/upload_download.spl | 14 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| nogc_sync_mut/gpu/engine2d/webgpu_surface.spl | 14 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_accel_metal.spl | 13 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_probe.spl | 62 | 49 | 49 | 79.0 | 18 | 72.2 | 86.1 | yes |
| gc_async_mut/gpu/engine2d/gpu_provider_probes.spl | 27 | 14 | 14 | 51.9 | 10 | 10.0 | 35.0 | yes |
| nogc_sync_mut/gpu/engine2d/sffi_opencl.spl | 32 | 19 | 19 | 59.4 | 5 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/bridge_game2d.spl | 36 | 24 | 24 | 66.7 | 7 | 28.6 | 50.0 | yes |
| gc_async_mut/gpu/engine2d/rendering_opt_provider.spl | 71 | 59 | 59 | 83.1 | 13 | 30.8 | 65.4 | yes |
| gc_async_mut/gpu/engine2d/backend_emu_adv.spl | 301 | 290 | 290 | 96.3 | 62 | 75.8 | 87.9 | yes |
| gc_async_mut/gpu/engine2d/backend_emu_math.spl | 32 | 21 | 21 | 65.6 | 11 | 72.7 | 77.3 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_target.spl | 11 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/generated_kernel_args.spl | 58 | 47 | 47 | 81.0 | 24 | 50.0 | 75.0 | yes |
| gc_async_mut/gpu/engine2d/helpers/clip_mask.spl | 10 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/helpers_clip.spl | 28 | 18 | 18 | 64.3 | 19 | 42.1 | 52.6 | yes |
| common/gpu/engine2d/gpu_epoch.spl | 74 | 66 | 66 | 89.2 | 40 | 72.5 | 86.2 | yes |
| gc_async_mut/gpu/engine2d/compute_dispatch.spl | 31 | 23 | 23 | 74.2 | 8 | 12.5 | 50.0 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_glass_material.spl | 126 | 118 | 118 | 93.7 | 30 | 76.7 | 86.7 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_runtime_adv.spl | 17 | 9 | 9 | 52.9 | 3 | 0.0 | 50.0 | yes |
| nogc_sync_mut/gpu/engine2d/backend_session.spl | 10 | 2 | 2 | 20.0 | 7 | 14.3 | 14.3 | yes |
| common/gpu/engine2d/scalar_oracle.spl | 106 | 99 | 99 | 93.4 | 32 | 71.9 | 85.9 | yes |
| gc_async_mut/gpu/engine2d/backend_capability.spl | 7 | 0 | 0 | 0.0 | 2 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/helpers_pixel.spl | 34 | 27 | 27 | 79.4 | 10 | 50.0 | 75.0 | yes |
| gc_async_mut/gpu/engine2d/backend_accel_cuda.spl | 6 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/bitmap_font_offload.spl | 75 | 69 | 69 | 92.0 | 24 | 66.7 | 83.3 | yes |
| nogc_sync_mut/gpu/engine2d/sffi_dispatch.spl | 15 | 9 | 9 | 60.0 | 7 | 14.3 | 35.7 | yes |
| gc_async_mut/gpu/engine2d/backend_accel_vulkan.spl | 5 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_intel_kernels.spl | 5 | 0 | 0 | 0.0 | 2 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_packed_owner_v3.spl | 36 | 31 | 31 | 86.1 | 10 | 70.0 | 85.0 | yes |
| nogc_sync_mut/gpu/engine2d/webgpu_sffi.spl | 5 | 0 | 0 | 0.0 | 2 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/engine2d_api.spl | 52 | 48 | 48 | 92.3 | 24 | 79.2 | 89.6 | yes |
| gc_async_mut/gpu/engine2d/rendering_parity_adapter.spl | 54 | 50 | 50 | 92.6 | 25 | 72.0 | 86.0 | yes |
| gc_async_mut/gpu/engine2d/vulkan_context_admission.spl | 14 | 10 | 10 | 71.4 | 6 | 16.7 | 58.3 | yes |
| gc_async_mut/gpu/engine2d/web_render_session.spl | 24 | 20 | 20 | 83.3 | 8 | 50.0 | 75.0 | yes |
| gc_async_mut/gpu/engine2d/backend_metal_runtime_ops.spl | 7 | 4 | 4 | 57.1 | 1 | 0.0 | 50.0 | yes |
| gc_async_mut/gpu/engine2d/backend_rocm_runtime_ops.spl | 3 | 0 | 0 | 0.0 | 1 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/vector_font_offload.spl | 54 | 51 | 51 | 94.4 | 19 | 84.2 | 89.5 | yes |
| gc_async_mut/gpu/engine2d/web_wm_session.spl | 19 | 16 | 16 | 84.2 | 2 | 100.0 | 100.0 | yes |
| nogc_sync_mut/gpu/engine2d/ffi_dispatch.spl | 15 | 12 | 12 | 80.0 | 7 | 28.6 | 50.0 | yes |
| gc_async_mut/gpu/engine2d/backend_metal_msl.spl | 2 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/helpers/text_fallback.spl | 2 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_vulkan_font_spirv.spl | 10 | 9 | 9 | 90.0 | 4 | 50.0 | 75.0 | yes |
| gc_async_mut/gpu/engine2d/backend_vulkan_glsl.spl | 1 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/color.spl | 71 | 45 | 70 | 98.6 | 25 | 80.0 | 90.0 | yes |
| gc_async_mut/gpu/engine2d/helpers_text.spl | 153 | 152 | 152 | 99.3 | 27 | 96.3 | 98.1 | yes |
| gc_async_mut/gpu/engine2d/host_ops.spl | 1 | 0 | 0 | 0.0 | 1 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/engine2d/strict_vulkan_rect_clip.spl | 21 | 20 | 20 | 95.2 | 10 | 40.0 | 70.0 | yes |
| common/gpu/engine2d/gpu_provider_conformance.spl | 27 | 27 | 27 | 100.0 | 16 | 100.0 | 100.0 | yes |
| common/gpu/engine2d/kernel_registry.spl | 71 | 71 | 71 | 100.0 | 21 | 95.2 | 97.6 | yes |
| gc_async_mut/gpu/engine2d/backend_cpu.spl | 2 | 2 | 2 | 100.0 | 0 | n/a | n/a | yes |
| gc_async_mut/gpu/engine2d/backend_cuda_font_ptx.spl | 1 | 1 | 1 | 100.0 | 2 | 0.0 | 50.0 | yes |
| gc_async_mut/gpu/engine2d/backend_cuda_kernels.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_cuda_launch_args.spl | 14 | 14 | 14 | 100.0 | 3 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/engine2d/backend_qualcomm.spl | 24 | 24 | 24 | 100.0 | 12 | 75.0 | 87.5 | yes |
| gc_async_mut/gpu/engine2d/backend_vulkan_affine_coverage_spirv.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_vulkan_blur_rect_spirv.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_vulkan_glass_material_spirv.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_vulkan_rect_batch_spirv.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_vulkan_shadow_rect_spirv.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_vulkan_spirv_raster_blobs.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/backend_vulkan_spirv.spl | 4 | 4 | 4 | 100.0 | 1 | 0.0 | 50.0 | yes |
| gc_async_mut/gpu/engine2d/bridge_drawing_compositor.spl | 12 | 12 | 12 | 100.0 | 1 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/ffi_cuda.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/ffi_intel.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/ffi_rocm.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/ffi_vulkan.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/font_owner.spl | 5 | 5 | 5 | 100.0 | 2 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/engine2d/framebuffer_hooks.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/framebuffer_surface.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/helpers/pixel_pack.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/host_gpu_draw_ir_event_flow.spl | 31 | 31 | 31 | 100.0 | 8 | 75.0 | 87.5 | yes |
| gc_async_mut/gpu/engine2d/__init__.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/mod.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/renderer_select.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/session_support.spl | 16 | 16 | 16 | 100.0 | 8 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/engine2d/sffi_cuda.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/sffi_intel.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/sffi_opencl.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/sffi_rocm.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/sffi_vulkan.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/simd_kernels.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/simd_provider.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/virtio_gpu_surface.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/engine2d/webgpu_surface.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| nogc_sync_mut/gpu/engine2d/cuda_session.spl | 32 | 32 | 32 | 100.0 | 9 | 100.0 | 100.0 | yes |
| nogc_sync_mut/gpu/engine2d/framebuffer_hooks.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| nogc_sync_mut/gpu/engine2d/metal_session.spl | 32 | 32 | 32 | 100.0 | 9 | 100.0 | 100.0 | yes |
| nogc_sync_mut/gpu/engine2d/simd_native_rows.spl | 4 | 4 | 4 | 100.0 | 2 | 100.0 | 100.0 | yes |
| nogc_sync_mut/gpu/engine2d/simd_provider.spl | 15 | 15 | 15 | 100.0 | 0 | n/a | n/a | yes |
| nogc_sync_mut/gpu/engine2d/webgpu_session.spl | 32 | 32 | 32 | 100.0 | 9 | 100.0 | 100.0 | yes |

## Simple web per file (sorted by uncovered executable lines, after)

`loaded=no` means no spec in the sweep imported the module at all.

| file (under src/lib/) | exec lines | hit before | hit after | line % after | decisions | both-outcome % | outcome % | loaded |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| gc_async_mut/gpu/browser_engine/webgl_context.spl | 2503 | 1913 | 1918 | 76.6 | 873 | 50.7 | 73.9 | yes |
| gc_async_mut/gpu/browser_engine/webgpu_context.spl | 800 | 421 | 421 | 52.6 | 236 | 19.1 | 47.2 | yes |
| gc_async_mut/gpu/browser_engine/js/parser.spl | 360 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/webgpu_commands.spl | 501 | 90 | 151 | 30.1 | 177 | 21.5 | 31.6 | yes |
| gc_async_mut/gpu/browser_engine/style_rule_index.spl | 576 | 232 | 232 | 40.3 | 168 | 13.1 | 30.1 | yes |
| gc_async_mut/gpu/browser_engine/dom_accessors.spl | 921 | 583 | 583 | 63.3 | 334 | 46.1 | 61.8 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_fractional_box_resolver.spl | 300 | 0 | 0 | 0.0 | 124 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/browser_engine/js/interpreter.spl | 258 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl | 1639 | 1408 | 1408 | 85.9 | 608 | 60.0 | 75.2 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl | 1039 | 837 | 837 | 80.6 | 342 | 46.2 | 68.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_foundation.spl | 1018 | 818 | 818 | 80.4 | 371 | 61.5 | 75.2 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl | 1297 | 1101 | 1101 | 84.9 | 358 | 58.7 | 75.8 | yes |
| gc_async_mut/gpu/browser_engine/net/cookie_store.spl | 316 | 121 | 121 | 38.3 | 93 | 76.3 | 86.6 | yes |
| gc_async_mut/gpu/browser_engine/web_opaque_box_qualification.spl | 329 | 144 | 144 | 43.8 | 127 | 12.6 | 33.1 | yes |
| gc_async_mut/gpu/browser_engine/js/lexer.spl | 184 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl | 169 | 0 | 0 | 0.0 | 89 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_raster.spl | 897 | 737 | 737 | 82.2 | 306 | 50.0 | 69.3 | yes |
| gc_async_mut/gpu/browser_engine/net/h1_client.spl | 581 | 427 | 427 | 73.5 | 217 | 47.0 | 66.4 | yes |
| gc_async_mut/gpu/browser_engine/webgpu_resources.spl | 309 | 160 | 160 | 51.8 | 128 | 6.2 | 39.1 | yes |
| gc_async_mut/gpu/browser_engine/style/supports.spl | 355 | 198 | 215 | 60.6 | 171 | 32.2 | 52.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_selectors.spl | 1615 | 1477 | 1477 | 91.5 | 553 | 75.4 | 85.2 | yes |
| gc_async_mut/gpu/browser_engine/web_corpus_case02_projection.spl | 129 | 0 | 0 | 0.0 | 67 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/browser_engine/webgpu_software_executor.spl | 204 | 89 | 89 | 43.6 | 60 | 16.7 | 40.8 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl | 384 | 274 | 274 | 71.4 | 134 | 38.1 | 58.6 | yes |
| gc_async_mut/gpu/browser_engine/browsing_context.spl | 108 | 6 | 6 | 5.6 | 19 | 57.9 | 65.8 | yes |
| gc_async_mut/gpu/browser_engine/script/js_transpiler.spl | 373 | 271 | 271 | 72.7 | 86 | 41.9 | 59.9 | yes |
| gc_async_mut/gpu/browser_engine/net/dns.spl | 161 | 62 | 62 | 38.5 | 52 | 5.8 | 27.9 | yes |
| gc_async_mut/gpu/browser_engine/net/websocket_client.spl | 99 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/net/cors.spl | 170 | 72 | 72 | 42.4 | 55 | 47.3 | 60.9 | yes |
| gc_async_mut/gpu/browser_engine/net/h2_hpack.spl | 111 | 18 | 18 | 16.2 | 32 | 12.5 | 14.1 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl | 659 | 566 | 566 | 85.9 | 222 | 58.1 | 75.7 | yes |
| gc_async_mut/gpu/browser_engine/web_render_backend.spl | 93 | 6 | 6 | 6.5 | 21 | 0.0 | 9.5 | yes |
| gc_async_mut/gpu/browser_engine/glass_comparison_runner.spl | 96 | 11 | 11 | 11.5 | 31 | 19.4 | 25.8 | yes |
| gc_async_mut/gpu/browser_engine/dom_color.spl | 539 | 428 | 458 | 85.0 | 271 | 33.6 | 65.5 | yes |
| gc_async_mut/gpu/browser_engine/net/h2_frame.spl | 305 | 0 | 229 | 75.1 | 216 | 13.9 | 42.6 | yes |
| gc_async_mut/gpu/browser_engine/widget_to_dom.spl | 273 | 199 | 199 | 72.9 | 76 | 44.7 | 61.2 | yes |
| gc_async_mut/gpu/browser_engine/js/values.spl | 73 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl | 791 | 718 | 718 | 90.8 | 263 | 64.6 | 81.2 | yes |
| gc_async_mut/gpu/browser_engine/script/js_compat.spl | 301 | 224 | 235 | 78.1 | 136 | 47.8 | 66.2 | yes |
| gc_async_mut/gpu/browser_engine/layout_core.spl | 81 | 18 | 18 | 22.2 | 18 | 16.7 | 22.2 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl | 788 | 726 | 726 | 92.1 | 291 | 71.1 | 84.4 | yes |
| gc_async_mut/gpu/browser_engine/script/script_host.spl | 91 | 34 | 34 | 37.4 | 29 | 24.1 | 32.8 | yes |
| gc_async_mut/gpu/browser_engine/security/permission_policy.spl | 84 | 27 | 27 | 32.1 | 25 | 68.0 | 84.0 | yes |
| gc_async_mut/gpu/browser_engine/net/h2_client.spl | 53 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/net/tls.spl | 80 | 29 | 29 | 36.2 | 28 | 28.6 | 35.7 | yes |
| gc_async_mut/gpu/browser_engine/style/animation_controller.spl | 50 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/text_painter.spl | 241 | 191 | 191 | 79.3 | 70 | 41.4 | 66.4 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl | 794 | 747 | 747 | 94.1 | 129 | 76.7 | 88.4 | yes |
| gc_async_mut/gpu/browser_engine/paint.spl | 174 | 130 | 130 | 74.7 | 55 | 27.3 | 57.3 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl | 381 | 337 | 337 | 88.5 | 138 | 58.0 | 75.4 | yes |
| gc_async_mut/gpu/browser_engine/dom.spl | 205 | 162 | 162 | 79.0 | 100 | 53.0 | 70.0 | yes |
| gc_async_mut/gpu/browser_engine/net/ws_handshake.spl | 89 | 46 | 46 | 51.7 | 28 | 7.1 | 30.4 | yes |
| gc_async_mut/gpu/browser_engine/js/dom_bridge.spl | 42 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/layout_table.spl | 328 | 286 | 286 | 87.2 | 103 | 67.0 | 81.6 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_css_rules.spl | 590 | 548 | 548 | 92.9 | 170 | 71.8 | 85.3 | yes |
| gc_async_mut/gpu/browser_engine/html_tokenizer.spl | 420 | 379 | 379 | 90.2 | 173 | 83.2 | 87.9 | yes |
| gc_async_mut/gpu/browser_engine/script/canvas_api.spl | 645 | 605 | 605 | 93.8 | 59 | 22.0 | 59.3 | yes |
| gc_async_mut/gpu/browser_engine/security/origin_policy.spl | 280 | 240 | 240 | 85.7 | 112 | 66.1 | 82.1 | yes |
| gc_async_mut/gpu/browser_engine/style/custom_properties.spl | 142 | 104 | 104 | 73.2 | 43 | 41.9 | 64.0 | yes |
| gc_async_mut/gpu/browser_engine/html_string_parser.spl | 176 | 139 | 139 | 79.0 | 37 | 43.2 | 66.2 | yes |
| gc_async_mut/gpu/browser_engine/glass_pipeline_compare.spl | 32 | 0 | 0 | 0.0 | 3 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/browser_engine/browser_renderer.spl | 73 | 43 | 43 | 58.9 | 11 | 72.7 | 77.3 | yes |
| gc_async_mut/gpu/browser_engine/net/h2_settings.spl | 29 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl | 1030 | 1001 | 1001 | 97.2 | 337 | 85.5 | 92.1 | yes |
| gc_async_mut/gpu/browser_engine/net/ws_frame_codec.spl | 133 | 0 | 105 | 78.9 | 31 | 71.0 | 83.9 | yes |
| gc_async_mut/gpu/browser_engine/script/simple_script.spl | 85 | 57 | 57 | 67.1 | 26 | 30.8 | 53.8 | yes |
| gc_async_mut/gpu/browser_engine/gpu_web/layout/adapter.spl | 145 | 118 | 118 | 81.4 | 75 | 58.7 | 75.3 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_render_session.spl | 121 | 95 | 95 | 78.5 | 38 | 42.1 | 55.3 | yes |
| gc_async_mut/gpu/browser_engine/dom_identity_index.spl | 230 | 205 | 205 | 89.1 | 83 | 69.9 | 83.1 | yes |
| gc_async_mut/gpu/browser_engine/layout_box.spl | 24 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/webgpu_status_errors.spl | 29 | 5 | 5 | 17.2 | 9 | 11.1 | 16.7 | yes |
| gc_async_mut/gpu/browser_engine/net/fetch.spl | 202 | 179 | 179 | 88.6 | 76 | 57.9 | 78.3 | yes |
| gc_async_mut/gpu/browser_engine/web_opaque_box_checks.spl | 69 | 46 | 46 | 66.7 | 33 | 39.4 | 65.2 | yes |
| gc_async_mut/gpu/browser_engine/security/cookie_policy.spl | 194 | 172 | 172 | 88.7 | 80 | 62.5 | 80.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_css_box_effects.spl | 283 | 261 | 261 | 92.2 | 87 | 71.3 | 85.6 | yes |
| gc_async_mut/gpu/browser_engine/net/ws_utils.spl | 134 | 69 | 113 | 84.3 | 72 | 45.8 | 70.1 | yes |
| gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl | 106 | 86 | 86 | 81.1 | 30 | 40.0 | 65.0 | yes |
| gc_async_mut/gpu/browser_engine/script/location_api.spl | 59 | 39 | 39 | 66.1 | 12 | 33.3 | 45.8 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl | 1062 | 1043 | 1043 | 98.2 | 344 | 81.7 | 90.8 | yes |
| gc_async_mut/gpu/browser_engine/chrome_webgpu_compute_evidence.spl | 93 | 78 | 78 | 83.9 | 38 | 50.0 | 72.4 | yes |
| gc_async_mut/gpu/browser_engine/gpu_web/text/cuda_line_break.spl | 99 | 85 | 85 | 85.9 | 41 | 29.3 | 61.0 | yes |
| gc_async_mut/gpu/browser_engine/net/cache.spl | 105 | 91 | 91 | 86.7 | 37 | 48.6 | 73.0 | yes |
| gc_async_mut/gpu/browser_engine/script/dom_api.spl | 96 | 82 | 82 | 85.4 | 29 | 55.2 | 72.4 | yes |
| gc_async_mut/gpu/browser_engine/script/form_api.spl | 56 | 42 | 42 | 75.0 | 27 | 63.0 | 74.1 | yes |
| gc_async_mut/gpu/browser_engine/style/animation.spl | 136 | 122 | 122 | 89.7 | 37 | 37.8 | 62.2 | yes |
| gc_async_mut/gpu/browser_engine/browser_renderer_utils.spl | 263 | 250 | 250 | 95.1 | 85 | 74.1 | 87.1 | yes |
| gc_async_mut/gpu/browser_engine/layout.spl | 186 | 173 | 173 | 93.0 | 58 | 72.4 | 84.5 | yes |
| gc_async_mut/gpu/browser_engine/net/h2_stream.spl | 13 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/style_block_parse.spl | 486 | 473 | 473 | 97.3 | 153 | 81.7 | 90.8 | yes |
| gc_async_mut/gpu/browser_engine/script/script_runner.spl | 33 | 21 | 21 | 63.6 | 5 | 0.0 | 30.0 | yes |
| gc_async_mut/gpu/browser_engine/style/computed.spl | 12 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/browser_script_execute.spl | 181 | 170 | 170 | 93.9 | 52 | 75.0 | 85.6 | yes |
| gc_async_mut/gpu/browser_engine/gpu_web/dom/dom_arena_types.spl | 98 | 87 | 87 | 88.8 | 35 | 60.0 | 74.3 | yes |
| gc_async_mut/gpu/browser_engine/script/worker_api.spl | 23 | 12 | 12 | 52.2 | 6 | 33.3 | 41.7 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_decl_apply.spl | 2008 | 1997 | 1997 | 99.5 | 606 | 69.5 | 84.7 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_geometry.spl | 139 | 128 | 128 | 92.1 | 46 | 63.0 | 81.5 | yes |
| gc_async_mut/gpu/browser_engine/web_paint_chunk_frame.spl | 112 | 101 | 101 | 90.2 | 27 | 48.1 | 74.1 | yes |
| gc_async_mut/gpu/browser_engine/selector_matcher.spl | 86 | 76 | 76 | 88.4 | 25 | 56.0 | 74.0 | yes |
| gc_async_mut/gpu/browser_engine/backend_screenshot_capture.spl | 84 | 75 | 75 | 89.3 | 28 | 28.6 | 64.3 | yes |
| gc_async_mut/gpu/browser_engine/browser_script_render.spl | 79 | 70 | 70 | 88.6 | 20 | 45.0 | 72.5 | yes |
| gc_async_mut/gpu/browser_engine/style/render_state.spl | 9 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/glass_demo_registry.spl | 8 | 0 | 0 | 0.0 | 1 | 0.0 | 0.0 | yes |
| gc_async_mut/gpu/browser_engine/net/entity/url_types.spl | 44 | 36 | 36 | 81.8 | 20 | 65.0 | 77.5 | yes |
| gc_async_mut/gpu/browser_engine/rendering_parity_adapter.spl | 82 | 74 | 74 | 90.2 | 19 | 42.1 | 71.1 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_cpu.spl | 27 | 19 | 19 | 70.4 | 10 | 20.0 | 50.0 | yes |
| gc_async_mut/gpu/browser_engine/style/transform.spl | 103 | 65 | 95 | 92.2 | 30 | 76.7 | 88.3 | yes |
| gc_async_mut/gpu/browser_engine/gpu_web/dom/dom_arena_build.spl | 139 | 132 | 132 | 95.0 | 16 | 87.5 | 93.8 | yes |
| gc_async_mut/gpu/browser_engine/html_tree_builder.spl | 362 | 355 | 355 | 98.1 | 193 | 58.5 | 79.3 | yes |
| gc_async_mut/gpu/browser_engine/style_block_resolve.spl | 321 | 314 | 314 | 97.8 | 121 | 86.8 | 93.0 | yes |
| gc_async_mut/gpu/browser_engine/web_showcase_tabs.spl | 37 | 30 | 30 | 81.1 | 16 | 43.8 | 71.9 | yes |
| gc_async_mut/gpu/browser_engine/layout_float.spl | 122 | 2 | 116 | 95.1 | 39 | 69.2 | 82.1 | yes |
| gc_async_mut/gpu/browser_engine/render_fixtures.spl | 302 | 296 | 296 | 98.0 | 83 | 61.4 | 75.9 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_file_renderer.spl | 44 | 38 | 38 | 86.4 | 13 | 46.2 | 73.1 | yes |
| gc_async_mut/gpu/browser_engine/script/event_loop.spl | 48 | 43 | 43 | 89.6 | 18 | 77.8 | 83.3 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_corpus_fixture_renderer.spl | 26 | 21 | 21 | 80.8 | 7 | 14.3 | 50.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles_gpu.spl | 101 | 96 | 96 | 95.0 | 21 | 52.4 | 76.2 | yes |
| gc_async_mut/gpu/browser_engine/style_invalidation.spl | 105 | 100 | 100 | 95.2 | 35 | 68.6 | 84.3 | yes |
| gc_async_mut/gpu/browser_engine/style_property_id.spl | 97 | 92 | 92 | 94.8 | 50 | 80.0 | 90.0 | yes |
| gc_async_mut/gpu/browser_engine/dom_visual_effects.spl | 97 | 0 | 93 | 95.9 | 29 | 58.6 | 79.3 | yes |
| gc_async_mut/gpu/browser_engine/web_draw_ir_damage_consumer.spl | 20 | 16 | 16 | 80.0 | 5 | 60.0 | 80.0 | yes |
| gc_async_mut/gpu/browser_engine/dom_color_named.spl | 127 | 124 | 124 | 97.6 | 45 | 86.7 | 93.3 | yes |
| gc_async_mut/gpu/browser_engine/net/entity/cookie_types.spl | 3 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/net/entity/request_types.spl | 4 | 1 | 1 | 25.0 | 4 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_box_geometry_provenance.spl | 79 | 76 | 76 | 96.2 | 28 | 82.1 | 91.1 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_url_placeholder_renderer.spl | 14 | 11 | 11 | 78.6 | 5 | 20.0 | 60.0 | yes |
| gc_async_mut/gpu/browser_engine/gpu_web/layout/manager.spl | 24 | 22 | 22 | 91.7 | 7 | 71.4 | 85.7 | yes |
| gc_async_mut/gpu/browser_engine/net/net_delegate.spl | 3 | 1 | 1 | 33.3 | 0 | n/a | n/a | yes |
| gc_async_mut/gpu/browser_engine/net/ws_crypto.spl | 160 | 108 | 158 | 98.8 | 45 | 91.1 | 95.6 | yes |
| gc_async_mut/gpu/browser_engine/resource_loader.spl | 33 | 31 | 31 | 93.9 | 13 | 76.9 | 88.5 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles.spl | 164 | 162 | 162 | 98.8 | 37 | 94.6 | 97.3 | yes |
| gc_async_mut/gpu/browser_engine/gpu_web/layout/cpu_execution_port.spl | 49 | 48 | 48 | 98.0 | 17 | 23.5 | 61.8 | yes |
| gc_async_mut/gpu/browser_engine/gpu_web/layout/invalidation.spl | 16 | 15 | 15 | 93.8 | 2 | 50.0 | 75.0 | yes |
| gc_async_mut/gpu/browser_engine/layout_paint.spl | 9 | 8 | 8 | 88.9 | 3 | 66.7 | 83.3 | yes |
| gc_async_mut/gpu/browser_engine/net/fetch_dispatch.spl | 2 | 1 | 1 | 50.0 | 0 | n/a | n/a | yes |
| gc_async_mut/gpu/browser_engine/script/clipboard_api.spl | 7 | 6 | 6 | 85.7 | 2 | 50.0 | 75.0 | yes |
| gc_async_mut/gpu/browser_engine/script/event_api.spl | 47 | 46 | 46 | 97.9 | 9 | 11.1 | 55.6 | yes |
| gc_async_mut/gpu/browser_engine/script/navigator_api.spl | 3 | 2 | 2 | 66.7 | 0 | n/a | n/a | yes |
| gc_async_mut/gpu/browser_engine/script/network_api.spl | 54 | 53 | 53 | 98.1 | 16 | 75.0 | 87.5 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_ssr_renderer.spl | 1 | 0 | 0 | 0.0 | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/style_block.spl | 308 | 307 | 307 | 99.7 | 107 | 90.7 | 95.3 | yes |
| gc_async_mut/gpu/browser_engine/web_decimal_geometry_diagnostic.spl | 3 | 2 | 2 | 66.7 | 1 | 0.0 | 50.0 | yes |
| gc_async_mut/gpu/browser_engine/browser_engine2d_bridge.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/browser_file_ops.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/containment.spl | 32 | 32 | 32 | 100.0 | 8 | 87.5 | 93.8 | yes |
| gc_async_mut/gpu/browser_engine/css.spl | 12 | 12 | 12 | 100.0 | 5 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/dom_limits.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/gpu_web/dom/__init__.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/gpu_web/__init__.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/gpu_web/layout/contracts.spl | 39 | 39 | 39 | 100.0 | 19 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/gpu_web/layout/__init__.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/gpu_web/text/__init__.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/html_fallback_renderer.spl | 234 | 234 | 234 | 100.0 | 52 | 82.7 | 91.3 | yes |
| gc_async_mut/gpu/browser_engine/html_named_character_references.spl | 10 | 10 | 10 | 100.0 | 2 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/js/ast.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/layout_inline.spl | 38 | 38 | 38 | 100.0 | 12 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/layout_insets.spl | 8 | 8 | 8 | 100.0 | 1 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/layout_m14_types.spl | 10 | 10 | 10 | 100.0 | 4 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/mod.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/net/browser_trust_store.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/net/entity/cache_types.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/net/entity/cors_types.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/net/entity/tls_types.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/script/console_api.spl | 25 | 25 | 25 | 100.0 | 5 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/script/console_buffer.spl | 15 | 15 | 15 | 100.0 | 3 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/script/js_simple_matrix.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/script/mod.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/script/storage_api.spl | 24 | 24 | 24 | 100.0 | 7 | 85.7 | 92.9 | yes |
| gc_async_mut/gpu/browser_engine/script/timer_api.spl | 4 | 4 | 4 | 100.0 | 0 | n/a | n/a | yes |
| gc_async_mut/gpu/browser_engine/shared/error.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/shared/logging.spl | 5 | 5 | 5 | 100.0 | 1 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_css_property_id.spl | 15 | 15 | 15 | 100.0 | 37 | 97.3 | 98.6 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_types.spl | 27 | 27 | 27 | 100.0 | 5 | 80.0 | 90.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/simple_web_html_renderer.spl | 7 | 7 | 7 | 100.0 | 1 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/simple_web_renderer.spl | 1 | 1 | 1 | 100.0 | 0 | n/a | n/a | yes |
| gc_async_mut/gpu/browser_engine/simple_web_script_placeholder_renderer.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/simple_web_script_renderer.spl | 8 | 8 | 8 | 100.0 | 3 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/webgl_render_commands.spl | 8 | 8 | 8 | 100.0 | 11 | 81.8 | 90.9 | yes |
| gc_async_mut/gpu/browser_engine/webgpu_types.spl | 0 | 0 | 0 | n/a | 0 | n/a | n/a | no |
| gc_async_mut/gpu/browser_engine/web_renderable_feature_inventory.spl | 95 | 95 | 95 | 100.0 | 40 | 100.0 | 100.0 | yes |
| gc_async_mut/gpu/browser_engine/web_renderable_feature_witness.spl | 92 | 92 | 92 | 100.0 | 43 | 95.3 | 97.7 | yes |

## Specs added in this branch (tests only, 316 examples)

| spec | examples | module measured for this spec alone |
|---|---:|---|
| engine2d/color_hex_named_spec | 15 | color.spl 49% |
| engine2d/draw_ir_box_corner_geometry_spec | 25 | draw_ir_box_effects.spl 39% |
| engine2d/host_gpu_queue_counters_spec | 11 | host_gpu_event_queue.spl 8% |
| engine2d/backend_software_shape_pixels_spec | 16 | backend_emu.spl 43%, backend_software.spl 11% |
| engine2d/vulkan_spirv_module_structure_spec | 23 | 18 SPIR-V blobs, 0 executable lines |
| browser_engine/ws_crypto_vectors_spec | 16 | net/ws_crypto.spl 98% |
| browser_engine/ws_frame_codec_rfc6455_spec | 25 | net/ws_frame_codec.spl 78% |
| browser_engine/h2_frame_codec_spec | 22 | net/h2_frame.spl 75% |
| browser_engine/webgl_render_command_ir_spec | 14 | webgl_render_commands.spl 87% |
| browser_engine/webgl_validation_tables_spec | 23 | webgl_context.spl 3% |
| browser_engine/webgpu_command_validation_spec | 16 | webgpu_commands.spl 12% |
| browser_engine/css_color_value_forms_spec | 33 | dom_color.spl 74% |
| browser_engine/css_transform_function_parse_spec | 16 | style/transform.spl 92% |
| browser_engine/css_box_shadow_and_supports_spec | 19 | dom_visual_effects.spl 95%, style/supports.spl 41% |
| browser_engine/js_compat_number_parsing_spec | 22 | script/js_compat.spl 58% |
| browser_engine/layout_float_placement_spec | 20 | layout_float.spl 95% |

Mutation proofs (source edited, spec run, source reverted with `git checkout`):

- `color.spl` `hex_to_color` 6-digit branch `rgba(r,g,b,255)` -> `rgba(g,r,b,255)`: 4 examples red (`expected 128 to equal 255`).
- `h2_frame.spl` `encode_frame` `sid_b1 = (stream_id / 256)` -> `/ 512`: 1 example red (`expected 1 to equal 3`).
- `ws_crypto.spl` `ws_word_to_bytes` swapped the two high bytes: RFC 6455 accept key, all three SHA-1 vectors and the word split red.
- `backend_emu.spl` `emu_draw_ellipse_filled` second-region span `2*x+1` -> `x+1`: 3 examples red (inside pixel black, area out of band, 48 mirror mismatches).

## Defects found while writing the specs (not fixed here — tests only)

- `src/lib/gc_async_mut/gpu/browser_engine/dom_visual_effects.spl:43` and `:61`
  call `WebBoxShadow.none()`, which is not defined on the struct
  (`browser_engine/css.spl:7`). `parse_box_shadows("none")`, `("")` or any
  layer with fewer than three tokens stops with
  `semantic: unknown static method none on class WebBoxShadow`. Expected: an
  empty layer list. The module has no importer inside `src/`, so the live path
  (`simple_web_css_box_effects.spl`) is unaffected. The same struct declares
  `color: text` while the parser stores a packed `u32`.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_baremetal_image_clip_spec.spl`
  and `baremetal_constructor_spec.spl` execute 0 examples on this seed:
  `cannot resolve import os.drivers.framebuffer.fb_driver` (`os` is not on the
  module path for a `test/01_unit/lib` spec).

Observed contracts worth knowing (asserted by the new specs, not defects):
`rt_host_gpu_queue_*` publishes the backend handle at submit and the payload
size/hash/text only at completion; WebSocket `decode_frame` returns a masked
frame's payload still masked (the client unmasks with `apply_mask`);
`dom_color.split_comma` does not trim its pieces.
