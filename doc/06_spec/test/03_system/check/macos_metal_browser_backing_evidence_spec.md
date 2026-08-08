# macOS Metal browser-backing evidence producer

> Validates the static contract for the macOS Metal browser-backing producer that feeds `scripts/check/check-macos-metal-render-log-compare.shs`.

<!-- sdn-diagram:id=macos_metal_browser_backing_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macos_metal_browser_backing_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macos_metal_browser_backing_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macos_metal_browser_backing_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS Metal browser-backing evidence producer

Validates the static contract for the macOS Metal browser-backing producer that feeds `scripts/check/check-macos-metal-render-log-compare.shs`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/macos_metal_browser_backing_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the static contract for the macOS Metal browser-backing producer that
feeds `scripts/check/check-macos-metal-render-log-compare.shs`.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/macos_metal_browser_backing_evidence_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- The producer captures Simple with the Metal backend, Chrome with GPU enabled
  through the DevTools path, and Electron through local Electron with browser
  target GPU metadata.
- The producer emits scoped `macos_metal_*_browser_backing_*` source-proof rows
  and pairwise ARGB diff status rows consumed by the strict compare wrapper.
- The stable default fixture avoids font raster differences so exact pairwise
  ARGB comparison can prove renderer equivalence without blur or tolerance.
- Electron capture uses offscreen OSR exact-sRGB mode on macOS so
  `BrowserWindow.capturePage()` does not inherit the display compositor's ICC
  transform while GPU browser-backing metadata is still collected separately.

## Operator Notes

Run this static spec on any host. Run
`scripts/check/check-macos-metal-browser-backing-evidence.shs` on macOS to
produce `build/macos-metal-browser-backing/evidence.env`, then run
`scripts/check/check-macos-metal-render-log-compare.shs` to validate the full
Metal render-log contract.

## Live Flow

1. The producer renders `test/fixtures/pixel_compare/css_boxes.html` through
   `tools/pixel_compare/render_simple_html.spl` with `PIXEL_BACKEND=metal`.
2. The producer renders the same fixture through Chrome with GPU enabled and a
   DevTools geometry output so `SystemInfo.getInfo` is available.
3. The producer renders the same fixture through the repo-local Electron binary
   under `tools/electron-shell/node_modules/.bin/electron` with offscreen paint
   enabled for exact sRGB pixels.
4. The producer writes `chrome-source.env` and `electron-source.env` with
   `macos_metal_chrome_browser_backing_*` and
   `macos_metal_electron_browser_backing_*` metadata rows.
5. The producer compares Simple, Chrome, and Electron ARGB buffers exactly and
   writes pairwise diff status rows.
6. The strict compare wrapper re-reads the env, source files, and ARGB artifacts
   before accepting the evidence.

## Evidence Files

- `build/macos-metal-browser-backing/evidence.env`
- `build/macos-metal-browser-backing/simple.argb.json`
- `build/macos-metal-browser-backing/chrome.argb.json`
- `build/macos-metal-browser-backing/electron.argb.json`
- `build/macos-metal-browser-backing/chrome-proof.json`
- `build/macos-metal-browser-backing/electron-proof.json`
- `build/macos-metal-browser-backing/chrome-source.env`
- `build/macos-metal-browser-backing/electron-source.env`
- `build/macos-metal-browser-backing/report.md`

## Required Rows

- `macos_metal_browser_backing_status=pass`
- `macos_metal_electron_browser_backing_status=pass`
- `macos_metal_electron_browser_backing_reason=electron-metal-backed`
- `macos_metal_chrome_browser_backing_status=pass`
- `macos_metal_chrome_browser_backing_reason=chrome-metal-backed`
- `macos_metal_pixel_comparison_status=pass`
- `macos_metal_pixel_comparison_mode=pairwise-argb-diff`
- `macos_metal_electron_chrome_pairwise_diff_status=pass`
- `macos_metal_electron_simple_pairwise_diff_status=pass`
- `macos_metal_chrome_simple_pairwise_diff_status=pass`
- `macos_metal_simple_argb_backend=metal`
- `macos_metal_electron_capture_compositor_mode=offscreen-osr-exact-srgb`
- `macos_metal_electron_capture_offscreen_paint=true`

## Failure Modes

- Missing macOS host leaves the producer unavailable; fixture evidence must not
  be copied from another platform.
- Missing repo-local Electron leaves the Electron backing row unavailable.
- Chrome capture without DevTools geometry is insufficient because GPU metadata
  may be absent even when a bitmap exists.
- A screenshot or ARGB artifact alone is not browser Metal proof.
- Metal metadata must be scoped under the `macos_metal_*_browser_backing_*`
  prefixes so the strict compare can validate source provenance.
- Exact pixel equality is required. The default fixture intentionally avoids
  font rasterization so this remains a backend/rendering proof instead of a font
  antialiasing comparison.
- Electron must use offscreen OSR exact-sRGB capture for the ARGB artifact.
  Windowed `capturePage()` on macOS can be color-managed through the display
  compositor and produce deterministic but non-sRGB fixture colors.
- The strict compare wrapper owns final pass/fail semantics; this producer only
  creates the browser evidence input.

## Completion Boundary

This producer proves desktop Simple, Chrome, and Electron Metal-backed browser
comparison on macOS. It does not prove optional strict Xcode GPU Frame Capture
or Tauri iOS/WKWebView Metal render-log evidence. Those lanes remain separate
inputs to `check-macos-metal-render-log-compare.shs`.

## Scenarios

### macOS Metal browser-backing evidence producer

#### keeps browser Metal proof and pairwise ARGB rows fail-closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-macos-metal-browser-backing-evidence.shs")

expect(script).to_contain("test/fixtures/pixel_compare/css_boxes.html")
expect(script).to_contain("PIXEL_BACKEND=metal")
expect(script).to_contain("CHROME_CAPTURE_DISABLE_GPU=false")
expect(script).to_contain("CHROME_CAPTURE_GEOMETRY_OUTPUT")
expect(script).to_contain("ELECTRON_CAPTURE_REMOTE_DEBUGGING_PORT")
expect(script).to_contain("ELECTRON_CAPTURE_OFFSCREEN_PAINT=1")
expect(script).to_contain("tools/electron-shell/node_modules/.bin/electron")
expect(script).to_contain("macos_metal_browser_backing_status")
expect(script).to_contain("macos_metal_electron_browser_backing_status")
expect(script).to_contain("macos_metal_chrome_browser_backing_status")
expect(script).to_contain("macos_metal_pixel_comparison_status")
expect(script).to_contain("pairwise-argb-diff")
expect(script).to_contain("macos_metal_electron_chrome_pairwise_diff_status")
expect(script).to_contain("macos_metal_electron_simple_pairwise_diff_status")
expect(script).to_contain("macos_metal_chrome_simple_pairwise_diff_status")
expect(script).to_contain("macos_metal_electron_capture_compositor_mode")
expect(script).to_contain("offscreen-osr-exact-srgb")
expect(script).to_contain("macos_metal_electron_capture_offscreen_paint")
expect(script).to_contain("macos_metal_")
expect(script).to_contain("browser_backing")
expect(script).to_contain("gpu_compositing=")
expect(script).to_contain("display_type=")
expect(script).to_contain("gl_implementation_parts=")
expect(script).to_contain("skia_backend_type=")
expect(script).to_contain("gl_renderer=")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
