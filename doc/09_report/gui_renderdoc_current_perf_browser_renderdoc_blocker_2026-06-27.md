# GUI RenderDoc Current Perf, Browser Backing, and RenderDoc Blocker - 2026-06-27

## Commands

Refresh retained 4K evidence:

```sh
ALLOW_PATH_SIMPLE_BIN=1 \
BUILD_DIR=build/widget-showcase-4k-200fps-current-2026-06-27 \
TIMEOUT_SECS=60 \
sh scripts/check/check-widget-showcase-4k-200fps.shs
```

Refresh retained 8K evidence:

```sh
ALLOW_PATH_SIMPLE_BIN=1 \
RESOLUTION=8k \
BUILD_DIR=build/widget-showcase-8k-perf-current-2026-06-27 \
TIMEOUT_SECS=90 \
sh scripts/check/check-widget-showcase-4k-200fps.shs
```

Aggregate confirmation:

```sh
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-2026-06-27/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-2026-06-27/status.env \
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env-check-current/evidence.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing-current/evidence.env \
BUILD_DIR=build/gui-renderdoc-current-2026-06-27-perf-browser \
REPORT_PATH=build/gui-renderdoc-current-2026-06-27-perf-browser/report.md \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Current 4K/8K Rows

| Evidence | Status | FPS x1000 | p50 ns | p95 ns | RSS kB | Source revision |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| 4K 200fps | `pass` (`met-200fps`) | 56818181 | 17600 | 17600 | 131328 / 262144 | `56a1985b1d38` |
| 8K perf | `pass` (`met-target-fps`) | 14021312 | 71320 | 71320 | 520192 / 750000 | `56a1985b1d38` |

Both rows were verified through the aggregate with
`GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1`:

```text
gui_showcase_4k_200fps_status=pass
gui_showcase_4k_200fps_source_revision=56a1985b1d38
gui_showcase_4k_200fps_current_source_revision=56a1985b1d38
gui_showcase_4k_200fps_source_revision_status=current
gui_showcase_8k_perf_status=pass
gui_showcase_8k_perf_source_revision=56a1985b1d38
gui_showcase_8k_perf_current_source_revision=56a1985b1d38
gui_showcase_8k_perf_source_revision_status=current
```

The browser backing row remains proven from the retained current evidence:

```text
gui_web_2d_vulkan_browser_backing_status=pass
```

## RenderDoc Blocker

This host exposes hardware Vulkan:

```text
gui_web_2d_vulkan_loader_status=present
gui_web_2d_vulkan_device=NVIDIA TITAN RTX
gui_web_2d_vulkan_driver=NVIDIA
```

RenderDoc was not available on `PATH` for this host check:

```text
gui_web_2d_vulkan_renderdoc_status=unavailable
gui_web_2d_vulkan_renderdoc_reason=missing-renderdoccmd-in-search-paths
```

The aggregate was incomplete at this 2026-06-27 capture point. Later Linux
refresh evidence proves browser backing, direct Electron/Chrome/Simple ARGB
artifacts, pairwise pixel equivalence, Web WM evidence, current-source 4K/8K
retained performance, and Simple/Chrome/Electron RenderDoc `RDOC` artifacts; do
not reopen those rows from this older report.

The Simple/Chrome/Electron Linux RenderDoc blockers in this report are
superseded by `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`
and `doc/09_report/linux_vulkan_render_log_compare_current_2026-07-02.md`.
Widget `.rdc` captures, platform render-log comparison on macOS/Windows, and
full CSS coverage beyond the implemented Simple Web subset remain separate
evidence lanes.
