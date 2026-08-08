# GUI RenderDoc Aggregate SSpec Perf

- status: improved
- baseline: `287129ms` for `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl`
- optimized cold-cache run: `48504ms`
- optimized wall time: `51.99s`
- max RSS: `192764 KB`
- scenarios: `11/11 passed`
- change: opt-in nested gate cache via `GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR`
- production mode: unchanged by default; cache is only used when the env var is set

## Commands

```sh
SIMPLE_LIB=src simple test test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl --mode=interpreter --clean --fail-fast --timeout 300
```

```sh
BUILD_DIR=build/normal-gui-renderdoc-aggregate \
REPORT_PATH=build/normal-gui-renderdoc-aggregate/report.md \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Evidence

- Cached SSpec run: passed `11/11`, duration `48507ms`, no perf-bug marker.
- Non-cached operator run: `gui_renderdoc_feature_coverage_status=incomplete`,
  `gui_renderdoc_feature_coverage_reason=missing-simple-widget-renderdoc`,
  `blocked_completion_gate_count=10`.
