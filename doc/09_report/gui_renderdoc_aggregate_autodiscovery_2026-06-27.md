# GUI RenderDoc Aggregate Autodiscovery - 2026-06-27

## Summary

The aggregate GUI RenderDoc checker now discovers current refresh evidence rows
without requiring every caller to pass explicit env overrides.

This closes a practical evidence-handoff gap: after 4K/8K and Linux
browser/Vulkan refresh runs produced passing rows, a plain aggregate invocation
still reported missing 4K/8K and failed browser/pixel rows because it only read
older canonical default paths.

## Verification

Focused SSpec:

```sh
release/x86_64-unknown-linux-gnu/simple test \
  test/03_system/check/gui_renderdoc_aggregate_autodiscovery_spec.spl \
  --mode=interpreter
```

Result: pass, 1 scenario.

Quiet default aggregate with current-source checking:

```sh
GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0 \
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache \
BUILD_DIR=build/goal-current-gui-renderdoc-autodiscovery-real \
REPORT_PATH=build/goal-current-gui-renderdoc-autodiscovery-real/report.md \
timeout 120s sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

Observed rows:

- `gui_showcase_4k_200fps_env=build/widget-showcase-4k-200fps-current-2026-06-27-refresh/status.env`
- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_8k_perf_env=build/widget-showcase-8k-perf-current-2026-06-27-refresh/status.env`
- `gui_showcase_8k_perf_status=pass`
- `gui_web_2d_vulkan_browser_backing_evidence_env=build/gui-web-2d-vulkan-env-browser-backing-current-refresh-electron/evidence.env`
- `gui_web_2d_vulkan_browser_backing_status=pass`
- `gui_web_2d_vulkan_direct_run_evidence_env=build/gui-web-2d-vulkan-env-run-current-refresh-electron/evidence.env`
- `gui_web_2d_vulkan_pixel_comparison_status=pass`
- `blocked_completion_gate_count=10`

## Boundary

This does not claim final completion. Remaining blockers are native RenderDoc
`.rdc` proof, Linux/macOS/Windows native render-log comparison, production
parity/font/Metal evidence, and full CSS coverage.
