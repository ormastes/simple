<!-- codex-research -->
# Graphics Backend Acceleration Local Research

Date: 2026-05-16

## Scope

Audit and plan performance-oriented graphics acceleration across:

- direct Engine2D apps in C vs Simple;
- Simple web-engine GUI apps vs Rust + Tauri apps;
- Simple web rendering vs Chrome/Chromium;
- window-manager new-window, resize, scroll, present, and idle behavior;
- GPU backends: Vulkan, CUDA, Metal, WebGPU/wgpu;
- CPU-only scalar and SIMD acceleration through the Simple optimization plugin model.

## Local Hardware

- NVIDIA RTX A6000 at `/dev/dri/renderD128`.
- NVIDIA TITAN RTX at `/dev/dri/renderD129`.
- NVIDIA driver `580.126.16`.
- Current shell has no `DISPLAY` or `WAYLAND_DISPLAY`, so desktop X11/Wayland tests are not available from this session.

## Existing Interfaces

- `RenderBackendCore` exists in `src/lib/gc_async_mut/gpu/engine2d/backend_core.spl`.
- `RenderBackendAdv` exists in `src/lib/gc_async_mut/gpu/engine2d/backend_adv.spl`.
- Combined `RenderBackend` and `Engine2DExtended` exist in `src/lib/gc_async_mut/gpu/engine2d/backend.spl`.
- The emulation layer exists in `backend_emu.spl`.

Conclusion: the common interface exists and should be preserved. The missing part is forced backend proof plus comparative performance evidence.

## Current Backend State

- CPU/software paths are the reliable fallback.
- CUDA backend exists and is structured as direct device rendering: device framebuffer, PTX module load, kernel launch, sync, readback.
- Vulkan backend exists, but currently calls GLSL compilation while the Rust runtime expects SPIR-V and returns unsupported for GLSL.
- Metal backend exists at the Simple layer but needs macOS-hosted runtime proof.
- WebGPU/wgpu hosted runtime is stubbed by default unless `webgpu-real` is enabled.

## Existing Perf Evidence

- `doc/08_tracking/baselines/engine2d_primitives.serial.log` proves a primitive frame renders in SimpleOS/QEMU, but is not a timing benchmark.
- `doc/01_research/local/simple_tauri.md` documents SimpleTauri architecture and flags software rasterization as a risk.
- `doc/05_design/host_wm_shell_backends.md` notes `tick_forever()` is a tight present loop and needs event sleeping or host event pumping.
- `doc/03_plan/chrome_modern_web_platform_compat_plan.md` covers compatibility and pixel comparison, but not performance parity.

## Missing Harnesses

1. Direct C vs Simple 2D benchmark using the same scene fixtures.
2. Rust+Tauri vs Simple GUI workflow benchmark.
3. Chrome vs Simple web-rendering trace benchmark.
4. Window-manager frame pacing and idle CPU benchmark.
5. CPU scalar vs CPU SIMD rendering benchmark tied to optimization provider metadata.

## Required Comparison Matrix

| Simple Surface | Reference | Metrics |
|---|---|---|
| Direct Engine2D app | C 2D app | frame time, pixels/sec, draw calls/sec, RSS, binary size, pixel hash |
| Simple GUI web app | Rust + Tauri app | startup, new window, resize, scroll, IPC, idle CPU/RSS |
| Simple web renderer | Chrome/Chromium | layout, paint, scroll, dropped frames, INP-style latency, pixel diff |
| CPU rendering | CPU scalar and C | SIMD speedup, scalar parity, active optimization providers |
| GPU rendering | CPU reference | forced backend, command time, readback time, pixel parity |

## Direct C vs Simple 2D Target

Use matched scene descriptions:

- clear full frame;
- 10k filled rectangles;
- mixed lines/circles/text;
- image blit and scaled blit;
- clipped scrolling list;
- dirty-rect dashboard update.

Targets:

- Simple CPU scalar within 1.25x of C on p50 frame time.
- Simple CPU SIMD/native equal or better than C for fill, blit, and clipped-scroll before claiming parity.
- GPU paths measured separately from CPU paths.

## Simple GUI vs Rust+Tauri Target

Equivalent workflows:

- cold start to first paint;
- open secondary window;
- close secondary window;
- resize and repaint;
- scroll 10k rows;
- route/page switch;
- IPC command round trip;
- event broadcast to two windows;
- idle CPU/RSS after 60 seconds.

Targets:

- Simple equal or better than Tauri on cold start or memory.
- Simple within 1.25x on p95 new-window, scroll, resize, and IPC latency before claiming Tauri-equivalent performance.
- Reports must identify the Tauri renderer and the Simple backend.

## Chrome vs Simple Web Target

Use same HTML/CSS/JS fixtures, viewport, fonts, and assets.

Metrics:

- first paint equivalent;
- layout time;
- paint/raster time;
- scroll p50/p95 frame time;
- dropped frames;
- interaction-to-next-paint-style latency;
- memory and GPU raster/backend state where available.

## Optimization Gaps

- Window manager needs event pump/sleep, dirty rectangles, present batching, and frame-pacing counters.
- Web engine needs style/layout cache invalidation, paint command batching, glyph/text cache, and scroll damage tracking.
- Engine2D needs span fill/copy, alpha blend, blit, and scroll kernels that can use CPU SIMD.
- Simple optimization plugin metadata must declare rendering vectorization providers and report provider hit/change counts.

