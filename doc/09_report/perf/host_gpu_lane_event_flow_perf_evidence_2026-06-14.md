# Host GPU Lane Event Flow Perf Evidence

Date: 2026-06-14
Scope: host_gpu_lane GUI/Engine2D event-flow and performance evidence plan
Status: baseline smoke recorded; full GUI/GPU runs pending on suitable host

## Claim To Prove

Host-owned UI/event semantics stay on the host lane, while coarse render,
resource, glyph, image, dirty-tile, and frame batches cross to the GPU lane by
canonical scheduling syntax:

```simple
target.later(lane: "frame", max_packet: 4096) gpu \:
    target.apply_draw_ir_delta(draw_ir_delta_ref)
```

The perf claim is accepted only when measured GPU-lane batches reduce p50 and
p95 frame or event-to-present time versus the current host/software path without
changing pixel hashes, event order, or fallback reporting.

## Current Event-Flow Surfaces

| Surface | File | Evidence Role |
|---|---|---|
| Host/GPU lane validator | `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl` | Rejects per-widget GPU dispatch, host semantic mutation on GPU, invalid lanes, and oversized packets; summarizes `baseline_ms` and `estimated_ms`. |
| Full render offload plan | `doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md` | Defines CPU host tree/events/layout -> Draw IR/Graph IR -> GPU render graph/raster/composite/present. |
| Host/GPU grammar system spec | `test/03_system/feature/language/host_gpu_lane_spec.spl` | Guards canonical `target.later(...) gpu \:` and `target.later(...) host \:` grammar. Do not edit for this lane. |
| GUI retained-frame baseline | `scripts/check/check-gtk-gui-size-speed-baseline.shs` | Emits cached BrowserBackend frame, no-op frame, present cache, retained Engine2D pixels, vector text render, GTK comparison, RSS, and ratio fields. |
| Engine2D scalar/GPU scene format | `test/05_perf/graphics_2d/README.md` and `test/05_perf/graphics_2d/*` | Defines `SCENE_RESULT` fields for fill, blit, and clipped-scroll p50/p95/hash comparisons across CPU, CUDA, Metal, and Simple runners. |
| WM/backend measurement exporters | `src/app/wm_compare/backend_measurement_export.spl` and `src/app/wm_compare/backend_measurement_software_export.spl` | Existing CLI surface for CUDA/device-buffer and software render-loop measurements used by GUI perf docs. |

## Required Baseline Fields

Every host/GPU lane perf report must include:

| Field | Meaning |
|---|---|
| `date`, `host`, `os`, `cpu`, `gpu`, `driver`, `simple_binary`, `mode` | Reproducibility metadata. |
| `scene`, `backend`, `lane`, `fallback_explicit` | Whether work ran on host, GPU, or a declared fallback. |
| `event_count`, `draw_ir_delta_count`, `packet_bytes`, `max_packet_bytes` | Event-flow and boundary size. |
| `frame_count`, `warmup_count`, `sample_count` | Timing sample contract. |
| `event_to_draw_ir_p50_ms`, `draw_ir_to_submit_p50_ms`, `submit_to_present_p50_ms`, `frame_p50_ms`, `frame_p95_ms` | Timing stages for less-ms proof. |
| `pixels_per_sec`, `draws_per_sec`, `rss_kb`, `pixel_hash` | Existing benchmark compatibility fields. |
| `baseline_frame_p50_ms`, `candidate_frame_p50_ms`, `speedup_x` | Required comparison fields. |

## Quick Baseline Recorded On This Host

Commands run:

```sh
bin/simple test test/05_perf/graphics_2d/webgpu_real_spec.spl --mode=interpreter
bin/simple run test/05_perf/graphics_2d/simple_runner.spl
```

Results:

| Surface | Result |
|---|---|
| WebGPU real probe spec | PASS: 12 tests, spec runtime 22 ms, total runner duration 29 ms. This is an availability/contract gate, not a frame-time benchmark. |
| `fill_1080p` smoke | `backend=simple_cpu_scalar`, 16x16 smoke, 3 frames, `p50_ns=186000`, `pixels_per_sec=1376344`, `draws_per_sec=543010`, `pixel_hash=1113616374`. |
| `blit_tiles` smoke | `backend=simple_cpu_scalar`, 16x16 smoke, 3 frames, `p50_ns=22000`, `pixels_per_sec=11636363`, `draws_per_sec=90909`, `pixel_hash=970686405`. |
| `clipped_scroll` smoke | `backend=simple_cpu_scalar`, 16x16 smoke, 3 frames, `p50_ns=16000`, `pixels_per_sec=16000000`, `draws_per_sec=687500`, `pixel_hash=3754790201`. |

These smoke values prove the parser/runtime surface is runnable here, but they
are too small for release claims. Use them only as harness health evidence.

## Pending Full Commands

Run these when the host has the native Simple binary and GPU/display stack
available:

```sh
SIMPLE_ENGINE2D_RUNNER_MODE=full bin/simple run test/05_perf/graphics_2d/simple_runner.spl

bin/simple run src/app/wm_compare/backend_measurement_export.spl -- \
  --measure-cuda-device-buffer true --width 1920 --height 1080

bin/simple run src/app/wm_compare/backend_measurement_software_export.spl -- \
  --software-render-backend software \
  --width 1920 --height 1080 --warmup-count 10 --sample-count 100

REPORT_PATH=doc/09_report/perf/host_gpu_lane_gtk_gui_size_speed_$(date -u +%F).md \
SIMPLE_ITERATIONS=10 GTK_ITERATIONS=200 \
scripts/check/check-gtk-gui-size-speed-baseline.shs
```

The GTK/native wrapper was not run in this pass because its default path may
native-build generated binaries, probe GTK/Xvfb, and run 200 GTK iterations; the
task asked for quick safe commands when available.

## Acceptance Thresholds

| Gate | Threshold |
|---|---|
| Correctness | Pixel hash or explicit readback checksum must match the host/software baseline for the same scene and resolution. |
| Event semantics | Event order, focus/drag/hit-test host commits, and accessibility-visible state remain host-owned; GPU lane must not mutate host semantics. |
| Boundary shape | GPU work uses coarse `target.later(...) gpu \:` batches; per-widget dispatch fails the evidence gate. |
| Fallback honesty | Missing GPU backend records `fallback_explicit=true` and is not counted as GPU speedup. |
| Frame speed | Candidate GPU lane `frame_p50_ms` <= 0.70x host/software baseline and `frame_p95_ms` <= 0.80x baseline at 1920x1080 or larger. |
| Event-to-present | Candidate `event_to_present_p50_ms` improves by at least 25% for dirty-tile and frame-batch scenes. |
| RSS | Candidate peak RSS is not more than 1.25x baseline unless the report explains persistent device-buffer/cache growth. |
| Samples | Full claim uses at least 10 warmup frames and 100 timed frames. |

