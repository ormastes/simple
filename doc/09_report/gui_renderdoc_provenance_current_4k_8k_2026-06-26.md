# GUI RenderDoc Aggregate 4K/8K Provenance Evidence - 2026-06-26

## Command

```bash
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-next/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-next/status.env \
BUILD_DIR=build/gui-renderdoc-provenance-check-next \
REPORT_PATH=build/gui-renderdoc-provenance-check-next/report.md \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Result

This 2026-06-26 aggregate status was incomplete at the time of capture:

- `gui_renderdoc_feature_coverage_status=incomplete`
- `gui_renderdoc_feature_coverage_reason=missing-simple-widget-renderdoc`
- `blocked_completion_gate_count=12`

The 4K and 8K retained showcase evidence is current and now carries Simple
binary provenance through the aggregate:

| Evidence | Status | FPS x1000 | p50 ns | p95 ns | Source revision | Simple binary source |
|----------|--------|-----------|--------|--------|-----------------|----------------------|
| 4K 200fps | pass (`met-200fps`) | 50025012 | 19990 | 19990 | current | path-opt-in |
| 8K perf | pass (`met-target-fps`) | 13452613 | 74335 | 74335 | current | path-opt-in |

Remaining blockers in this report were RenderDoc/browser/platform parity gates,
not the retained 4K/8K perf rows. The Linux Simple/Chrome/Electron RenderDoc and
browser-backing blockers are superseded by
`doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`
and `doc/09_report/linux_vulkan_render_log_compare_current_2026-07-02.md`, which
record zero blocked Linux RenderDoc gates with `RDOC` artifacts. Widget
RenderDoc, macOS/Windows render-log comparison, production parity/font/readback
evidence, and full CSS coverage remain separate evidence lanes.
