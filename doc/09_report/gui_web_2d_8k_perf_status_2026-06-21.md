# GUI/Web/2D 8K Perf Status — 2026-06-21

## Evidence

Command:

```bash
SIMPLE_LIB=src bin/simple run examples/06_io/ui/showcase_8k_scroll_gui.spl
```

Result: exit 0.

Smoke viewport: 1280x800, 1,024,000 px.

Correctness:

- ON scroll path equals OFF full repaint with byte-identical buffers.

Default smoke metrics:

| Scenario | OFF mean | ON mean | Dirty pixels | Result |
| --- | ---: | ---: | ---: | --- |
| idle | 189331us | <1us | 0 | retained path skips unchanged frame |
| steady scroll | 189656us | 102040us | 63216 | ~1.8x raster-stage speedup |

The benchmark prints this present limitation: no sub-rect present extern exists,
so on-window present still has a full-frame upload ceiling.

## Full 8K Status

Full 8K proof is not claimed by this run.

Missing retained full-8K evidence row:

- viewport: 7680x4320
- backend: GUI/web/2D backend under test
- binary/source revision
- readback mode and checksum/readback proof
- p50/p95 timing
- RSS or memory budget
- fallback state

Blocker: `8k-host-unavailable-for-this-turn`.

The default smoke run is useful regression evidence, but it must not be counted
as a full 8K GUI/web/2D performance pass.

## Follow-up Evidence Wrapper

`scripts/check/check-widget-showcase-4k-200fps.shs` now emits retained
showcase RSS rows for both `RESOLUTION=4k` and `RESOLUTION=8k`:

- `gui_showcase_8k_perf_max_rss_kb`
- `gui_showcase_8k_perf_max_rss_budget_kb`
- `gui_showcase_8k_perf_rss_status`
- `gui_showcase_8k_perf_time_log`

Set `MAX_RSS_KB` to enforce a memory budget. With the default `MAX_RSS_KB=0`,
the wrapper records measured RSS without enforcing a budget.

## Budgeted 8K Retained Showcase Evidence — 2026-06-23

Command:

```bash
RESOLUTION=8k MAX_RSS_KB=1048576 \
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple \
BUILD_DIR=build/widget-showcase-8k-perf-budget TIMEOUT_SECS=120 \
sh scripts/check/check-widget-showcase-4k-200fps.shs
```

Result: pass.

- viewport: 7680x4320
- pixels: 33177600
- frames: 120
- retained render mode: `retained-static-frame`
- redraw frames: 1
- checksum: 894747485546
- nonzero pixels: 209
- target FPS: 200
- measured FPS x1000: 13718989
- RSS: 520192 KiB
- RSS budget: 1048576 KiB
- RSS status: pass

Aggregate propagation:

```bash
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-budget/status.env \
BUILD_DIR=build/gui_renderdoc_feature_coverage_status_with_8k_budget \
REPORT_PATH=doc/09_report/gui_renderdoc_feature_coverage_status_with_8k_budget_2026-06-23.md \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

Result: the aggregate report includes
`GUI/web/2D 8K retained perf: pass (met-target-fps; fps_x1000 13718989; rss 520192/1048576 kB)`.

Scope: this proves the retained static 8K showcase path has checksum/readback,
FPS, and enforced RSS-budget evidence. It does not by itself clear the remaining
RenderDoc, browser Vulkan backing, or font-offload blockers in the aggregate GUI
hardening goal.
