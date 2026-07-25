# GUI RenderDoc Widget Source Contract Evidence - 2026-06-26

## Command

```bash
GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 \
GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps-current-next/status.env \
GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf-current-next/status.env \
BUILD_DIR=build/gui-renderdoc-widget-source-contract-next \
REPORT_PATH=build/gui-renderdoc-widget-source-contract-next/report.md \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Result

The aggregate remains incomplete, but now exposes the exact widget RenderDoc
source evidence files and required contracts:

- `gui_renderdoc_feature_coverage_status=incomplete`
- `gui_renderdoc_feature_coverage_reason=missing-simple-widget-renderdoc`
- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_8k_perf_status=pass`

Simple widget gate:

- source env: `build/renderdoc/widget-probe-small/simple/evidence.env`
- source env status: `missing`
- generation command: `RDOC_OUTPUT_DIR=build/renderdoc/widget-probe-small RDOC_SIMPLE_PROG="$PWD/src/app/test/renderdoc_vulkan_widget_capture.spl" RDOC_HTML_PATH="$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html" scripts/tool/renderdoc-evidence.shs capture-simple`
- required backend: `simple`
- required scene: `vulkan-engine2d`
- required program: `src/app/test/renderdoc_vulkan_widget_capture.spl`
- required HTML suffix: `test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html`
- required magic: `RDOC`

Electron widget gate:

- source env: `build/renderdoc/electron-display-helper/electron-html/evidence.env`
- source env status: `missing`
- generation command: `RDOC_OUTPUT_DIR=build/renderdoc/electron-display-helper RDOC_HTML_PATH="$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html" scripts/tool/renderdoc-evidence.shs capture-electron-html`
- required backend: `electron`
- required scene: `html-css-electron`
- required HTML suffix: `test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html`
- required magic: `RDOC`
