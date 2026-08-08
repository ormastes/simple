# GUI Showcase 4K/8K Self-Hosted Perf Evidence - 2026-06-27

## Summary

Fresh retained widget-showcase performance rows pass for the current source
revision using the repo self-hosted release binary
`release/x86_64-unknown-linux-gnu/simple`. Both rows build a native ELF alias,
run with `fallback_state=none`, scan the full readback buffer, and pass RSS
budgets. A 4K row was refreshed after narrowing the generated alias to retained
perf code and changing default binary discovery to prefer release/self-hosted
binaries before `bin/simple`. The canonical 8K build directory was refreshed
after that wrapper fix so the aggregate no longer reads stale Rust-seed 8K
evidence. A later refresh after the plan-only Simple-binary status fix produced
current source revision `74744b04ae2d` for both 4K and 8K rows; strict aggregate
source freshness accepted both rows as current.

This proves the current retained 4K/8K showcase perf contract for this host. It
does not prove RenderDoc `.rdc`, Chrome/Electron Vulkan backing, macOS Metal,
Windows D3D12, production GUI/web parity, or full CSS coverage.

## Commands

```sh
BUILD_DIR=build/widget-showcase-4k-200fps-current-2026-06-27-self-hosted \
TIMEOUT_SECS=60 \
sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k \
BUILD_DIR=build/widget-showcase-8k-perf-current-2026-06-27-self-hosted \
TIMEOUT_SECS=90 \
sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k \
BUILD_DIR=build/widget-showcase-8k-perf \
TIMEOUT_SECS=90 \
sh scripts/check/check-widget-showcase-4k-200fps.shs

GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-2026-06-27-self-hosted/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-2026-06-27-self-hosted/status.env \
BUILD_DIR=build/gui-renderdoc-current-2026-06-27-self-hosted-perf \
REPORT_PATH=build/gui-renderdoc-current-2026-06-27-self-hosted-perf/report.md \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-current-2026-06-27-self-hosted-perf-cache \
GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0 \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs

BUILD_DIR=build/widget-showcase-4k-200fps-current-2026-06-27-after-simple-status \
TIMEOUT_SECS=60 \
sh scripts/check/check-widget-showcase-4k-200fps.shs

RESOLUTION=8k \
BUILD_DIR=build/widget-showcase-8k-perf-current-2026-06-27-after-simple-status \
TIMEOUT_SECS=90 \
sh scripts/check/check-widget-showcase-4k-200fps.shs

GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-2026-06-27-after-simple-status/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-2026-06-27-after-simple-status/status.env \
BUILD_DIR=build/gui-renderdoc-current-2026-06-27-after-simple-status-perf \
REPORT_PATH=build/gui-renderdoc-current-2026-06-27-after-simple-status-perf/report.md \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-renderdoc-current-2026-06-27-after-simple-status-perf-cache \
GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0 \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Evidence

| Row | Status | FPS x1000 | RSS KiB | Binary Source | Native Format | Fallback | Source Status |
| --- | --- | ---: | --- | --- | --- | --- | --- |
| 4K after Simple-status fix | pass (`met-200fps`) | 56195560 | 131328 / 262144 | self-hosted-release | pass | none | current (`74744b04ae2d`) |
| 8K after Simple-status fix | pass (`met-target-fps`) | 14015416 | 519680 / 750000 | self-hosted-release | pass | none | current (`74744b04ae2d`) |
| 4K 200fps refreshed | pass (`met-200fps`) | 61766522 | 131328 / 262144 | self-hosted-release | pass | none | current (`7ff296568c26`) |
| 4K 200fps | pass (`met-200fps`) | 53763440 | 131328 / 262144 | self-hosted-release | pass | none | current |
| 8K perf refreshed | pass (`met-target-fps`) | 15291688 | 519680 / 750000 | self-hosted-release | pass | none | current (`7ff296568c26`) |
| 8K perf | pass (`met-target-fps`) | 15281173 | 519680 / 750000 | self-hosted-release | pass | none | current |

Readback proof:

- 4K after Simple-status fix: `3840x2160`, `8294400` pixels, `5458` nonzero
  pixels, checksum `23357114226484`, retained static frame, redraw frames `1`,
  frame p50/p95 `17795` ns.
- 8K after Simple-status fix: `7680x4320`, `33177600` pixels, `203` nonzero
  pixels, checksum `869060580878`, retained static frame, redraw frames `1`,
  frame p50/p95 `71350` ns.
- 4K refreshed: `3840x2160`, `8294400` pixels, `5458` nonzero pixels, checksum
  `23357114226484`, retained static frame, redraw frames `1`, frame average
  `16190` ns.
- 4K prior: `3840x2160`, `8294400` pixels, `5458` nonzero pixels, checksum
  `23357114226484`, retained static frame, redraw frames `1`.
- 8K: `7680x4320`, `33177600` pixels, `203` nonzero pixels, checksum
  `869060580878`, retained static frame, redraw frames `1`, frame average
  `65395` ns.

## Aggregate Status After Refresh

After refreshing `build/widget-showcase-8k-perf/status.env`, the aggregate
reports:

- `gui_showcase_8k_perf_status=pass`
- `gui_showcase_8k_perf_source_revision_status=current`
- `gui_showcase_8k_perf_simple_bin=release/x86_64-unknown-linux-gnu/simple`
- `gui_showcase_8k_perf_simple_bin_source=self-hosted-release`
- `gui_showcase_8k_perf_frame_elapsed_ns_status=pass`
- `blocked_completion_gate_count=8`

After the Simple-status fix refresh, strict aggregate source freshness reports:

- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_4k_200fps_source_revision_status=current`
- `gui_showcase_4k_200fps_current_source_revision=74744b04ae2d`
- `gui_showcase_4k_200fps_simple_bin_status=pass`
- `gui_showcase_8k_perf_status=pass`
- `gui_showcase_8k_perf_source_revision_status=current`
- `gui_showcase_8k_perf_current_source_revision=74744b04ae2d`
- `gui_showcase_8k_perf_simple_bin_status=pass`
- `blocked_completion_gate_count=8`

After hardening the default source fingerprint to include the Simple Web
renderer implementation, fresh strict aggregate source freshness reports:

- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_4k_200fps_source_revision_status=current`
- `gui_showcase_4k_200fps_current_source_revision=b996d435cff9`
- `gui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- `gui_showcase_4k_200fps_fps_x1000=62034739`
- `gui_showcase_4k_200fps_frame_p95_ns=16120`
- `gui_showcase_8k_perf_status=pass`
- `gui_showcase_8k_perf_source_revision_status=current`
- `gui_showcase_8k_perf_current_source_revision=b996d435cff9`
- `gui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- `gui_showcase_8k_perf_fps_x1000=14035087`
- `gui_showcase_8k_perf_frame_p95_ns=71250`
- `blocked_completion_gate_count=8`

The remaining aggregate blockers are Chrome/Electron RenderDoc `.rdc` capture,
Electron widget RenderDoc `.rdc`, native render-log comparison across Linux
Vulkan/macOS Metal/Windows D3D12, production GUI/web readback/parity gates, and
full CSS rendering coverage beyond the implemented subset.

## Current Blocker

The repo `bin/simple` launcher path still fails this native-build lane on this
host with `semantic: invalid assignment: unsupported assignment target`. The
perf wrapper now avoids that stale/slow path by defaulting to the release
self-hosted binary first; the underlying compiler/runtime bug is tracked in
`doc/08_tracking/bug/gui_showcase_4k_bin_simple_native_assignment_target_2026-06-27.md`.

## Aggregate Boundary

The aggregate remains `incomplete` after accepting these perf rows because the
run intentionally did not provide the remaining platform/browser/RenderDoc
parity evidence.
