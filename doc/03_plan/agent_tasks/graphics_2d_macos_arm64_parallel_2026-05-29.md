# Graphics 2D macOS ARM64 Parallel Tracking Note - 2026-05-29

## Scope

This lane supports the broad GUI/WM/rendering restart objective by keeping the
macOS ARM64 2D graphics performance evidence honest and separate from
Linux-host renderer evidence.

Owned tracking doc:

- `doc/08_tracking/perf/graphics_2d_macos_arm64_2026-05-16.md`

Current renderer restart plan inspected:

- `doc/03_plan/gui_renderer_restart_plan_2026-05-29.md`

## Status

- CPU proof: completed on macOS ARM64. The C scalar reference was rebuilt from
  source with host `clang -O2` and measured on Apple M4 for `fill_1080p`,
  `blit_tiles`, and `clipped_scroll`.
- Metal availability proof: completed as an unavailable/stub proof on macOS
  ARM64. `rt_metal_is_available()` returned `false` on Apple M4, so
  `rt_metal_init()` and Metal draw/readback paths were not reached.
- CUDA benchmark evidence: not relevant to macOS Metal. The existing Simple
  GPU benchmark attempts `libcuda.so` and fails gracefully because CUDA is not
  present on Apple Silicon.
- Batch benchmark evidence: not usable for macOS Metal as written. The file has
  invalid brace-style Simple syntax and CUDA extern calls.
- Vulkan/Linux evidence: belongs to the Engine2D CPU/Vulkan lane only. It
  cannot prove Apple Metal, Cocoa, or macOS ARM64 GPU behavior.

## Remaining macOS-Required Evidence

- Run on Apple Silicon with a runtime where `rt_metal_is_available()` returns
  `true`.
- Prove `rt_metal_init()` succeeds and records concrete device/context status.
- Run a Metal smoke that clears/draws and validates sync readback pixel hashes.
- Compare Metal-backed Engine2D output against the CPU baseline for matching
  scenes, dimensions, and hashes.
- Capture Metal p50/p95 timing, pixels/sec, draws/sec, and macOS memory
  evidence where the platform exposes it.
- Capture on-screen macOS window evidence separately if GUI presentation is
  included in the lane.
- Ensure the benchmark used for final proof parses under current Simple syntax
  and uses Metal runtime entry points, not CUDA entry points.

## Lane Result

The macOS ARM64 graphics lane is complete as a restart tracking/evidence lane:
it has a valid CPU baseline and a valid Metal-unavailable/stub finding. It does
not yet have Metal correctness or Metal performance evidence; those remain
macOS/Apple-Silicon follow-up gates, not Linux/Vulkan proof. Linux/Vulkan checks
must remain classified as host-limited evidence for a different backend lane.
