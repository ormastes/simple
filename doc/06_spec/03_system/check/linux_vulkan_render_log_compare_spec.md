# Linux Vulkan render-log compare gate

> Validates the Linux-first normalized render-log gate for Simple, Chrome, and Electron Vulkan evidence. The spec uses controlled key/value fixtures so it can run on non-GUI hosts without launching browsers or RenderDoc.

<!-- sdn-diagram:id=linux_vulkan_render_log_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linux_vulkan_render_log_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linux_vulkan_render_log_compare_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linux_vulkan_render_log_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux Vulkan render-log compare gate

Validates the Linux-first normalized render-log gate for Simple, Chrome, and Electron Vulkan evidence. The spec uses controlled key/value fixtures so it can run on non-GUI hosts without launching browsers or RenderDoc.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/linux_vulkan_render_log_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Linux-first normalized render-log gate for Simple, Chrome, and
Electron Vulkan evidence. The spec uses controlled key/value fixtures so it can
run on non-GUI hosts without launching browsers or RenderDoc.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/linux_vulkan_render_log_compare_spec.spl --mode=interpreter --clean --fail-fast
```

## Operator Flow

1. Produce direct GUI/web/2D Vulkan run evidence with
   `scripts/setup/setup-gui-web-2d-vulkan-env.shs --run`.
2. Produce focused browser GPU-status evidence with
   `scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing`.
3. Run `scripts/check/check-linux-vulkan-render-log-compare.shs` with
   `GUI_WEB_2D_VULKAN_ENV` pointing at the direct-run evidence and
   `GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV` pointing at the focused
   browser-backing evidence.
4. Treat `linux_vulkan_render_log_compare_status=pass` as a Linux-only result.
   macOS Metal and Windows D3D12 have separate compare gates and must not be
   inferred from the Linux row.

## Evidence Contract

The Linux compare gate reads pixel equivalence from the direct-run evidence:

- `gui_web_2d_vulkan_pixel_comparison_status=pass`
- `gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff`
- `gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass`
- `gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass`
- `gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass`

It reads browser Vulkan proof from the focused browser-backing evidence when
that file exists:

- `gui_web_2d_vulkan_browser_backing_status=pass`
- `gui_web_2d_vulkan_electron_browser_backing_status=pass`
- `gui_web_2d_vulkan_chrome_browser_backing_status=pass`

The fallback to `GUI_WEB_2D_VULKAN_ENV` exists only for older fixtures that
store both direct-run and browser-backing fields in the same env file.

## Failure Semantics

The gate is fail-closed. If Electron hardware Vulkan backing fails, the Linux
row must report `electron-browser-backing-fail`; if Chrome is proven pass in
the focused browser env, the reason must not report Chrome as missing. Missing
RenderDoc `.rdc` evidence is required by default. Missing or failed Simple,
Chrome, or Electron RenderDoc rows are reported through
`linux_vulkan_render_log_compare_renderdoc_*_status` and make
`linux_vulkan_render_log_compare_status=fail`. Set
`LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0` only for diagnostic partial-log runs.

## Normalized Outputs

The wrapper writes one rollup env and four Simple render-log env files:

- `evidence.env` contains `linux_vulkan_render_log_compare_*` keys for the
  platform-matrix gate.
- `simple.srl.env` records the Simple Vulkan source in `simple-render-log-v1`
  format.
- `chrome.srl.env` records the Chrome source in `simple-render-log-v1` format.
- `electron.srl.env` records the Electron source in `simple-render-log-v1`
  format.
- `compare.srl.env` records the pairwise comparison result and references the
  direct-run evidence file.

Each source log records platform, native API, source name, capture tool,
backend, scene, viewport, nonblank count, artifact path, artifact magic, and a
native-info field for backend details not yet represented by the normalized
schema.

## Test Matrix

The spec covers seven cases:

1. A combined fixture where direct-run, browser-backing, pairwise diff, and
   RenderDoc statuses all pass. This proves the pass contract and source-log
   shape.
2. A combined fixture where Electron browser backing fails. This proves the
   gate remains failed even when Simple Vulkan and pairwise pixels pass.
3. A split fixture where direct-run pixels and focused browser-backing evidence
   live in separate files. This proves current real host evidence is interpreted
   precisely: Chrome can be pass while Electron is fail, without reporting
   Chrome as missing.
4. A fresh main `--browser-backing` fixture plus a stale focused env. This proves
   the wrapper does not let stale focused evidence override the current backing
   run.
5. A RenderDoc failure fixture where Chrome fails with a concrete crash reason.
   This proves the normalized Linux rollup fails closed by default and Chrome
   source log preserves failure detail for platform-agent comparison.
6. A diagnostic RenderDoc failure fixture with strict RenderDoc disabled. This
   proves partial native logs can still be inspected without claiming platform
   completion.
7. A fixture with blank and mismatched ARGB rows. This proves pairwise status
   alone cannot pass without comparable nonblank source pixels.
8. A source contract check that keeps the default RenderDoc evidence paths on
   the focused current-capture rows instead of stale canonical probe rows.

## Completion Boundaries

`linux_vulkan_render_log_compare_status=pass` only proves the Linux Vulkan row.
It does not prove macOS Metal, Windows D3D12, production GUI/web parity, full
CSS rendering, or RenderDoc completion. The aggregate audit must still combine
this row with `macos_metal_render_log_compare_*` and
`windows_d3d12_render_log_compare_*` before the native platform matrix can pass.

## Scenarios

### Linux Vulkan render-log compare gate

#### accepts matching Linux Vulkan Simple Chrome and Electron fixture evidence

- Create pass fixtures for aggregate and RenderDoc evidence
   - Expected: code equals `0`
- Read normalized pass evidence and source logs


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create pass fixtures for aggregate and RenderDoc evidence")
val command = "rm -rf build/test-linux-vulkan-render-log-pass && mkdir -p build/test-linux-vulkan-render-log-pass/rdoc/simple build/test-linux-vulkan-render-log-pass/rdoc/html build/test-linux-vulkan-render-log-pass/rdoc/electron && cat > build/test-linux-vulkan-render-log-pass/gui.env <<'EOF'\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_simple_argb_width=3840\n" +
    "gui_web_2d_vulkan_simple_argb_height=2160\n" +
    "gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_chrome_argb_width=3840\n" +
    "gui_web_2d_vulkan_chrome_argb_height=2160\n" +
    "gui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_electron_argb_width=3840\n" +
    "gui_web_2d_vulkan_electron_argb_height=2160\n" +
    "gui_web_2d_vulkan_electron_argb_nonblank_pixel_count=42\n" +
    "EOF\n" +
    "printf 'rdoc_simple_gate_status=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\nrdoc_capture_file=simple.rdc\\n' > build/test-linux-vulkan-render-log-pass/rdoc/simple/evidence.env\n" +
    "printf 'rdoc_external_host_capture_gate_status=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\nrdoc_capture_file=chrome.rdc\\n' > build/test-linux-vulkan-render-log-pass/rdoc/html/evidence.env\n" +
    "printf 'rdoc_electron_html_gate_status=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\nrdoc_capture_file=electron.rdc\\n' > build/test-linux-vulkan-render-log-pass/rdoc/electron/evidence.env\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-pass/out REPORT_PATH=build/test-linux-vulkan-render-log-pass/out/report.md GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-pass/gui.env RDOC_SIMPLE_EVIDENCE_ENV=build/test-linux-vulkan-render-log-pass/rdoc/simple/evidence.env RDOC_HTML_EVIDENCE_ENV=build/test-linux-vulkan-render-log-pass/rdoc/html/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-linux-vulkan-render-log-pass/rdoc/electron/evidence.env sh scripts/check/check-linux-vulkan-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read normalized pass evidence and source logs")
val evidence = file_read("build/test-linux-vulkan-render-log-pass/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_required_api=vulkan")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_status=pass")
val electron_log = file_read("build/test-linux-vulkan-render-log-pass/out/electron.srl.env")
expect(electron_log).to_contain("simple_render_log_format=simple-render-log-v1")
expect(electron_log).to_contain("simple_render_log_platform=linux")
expect(electron_log).to_contain("simple_render_log_native_api=vulkan")
expect(electron_log).to_contain("simple_render_log_source=electron")
```

</details>

#### fails closed when Electron Vulkan backing is not proven

- Create fail fixtures with Electron browser backing disabled
   - Expected: code equals `0`
- Read fail-closed evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create fail fixtures with Electron browser backing disabled")
val command = "rm -rf build/test-linux-vulkan-render-log-fail && mkdir -p build/test-linux-vulkan-render-log-fail && cat > build/test-linux-vulkan-render-log-fail/gui.env <<'EOF'\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=fail\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_browser_backing_status=fail\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_simple_argb_width=3840\n" +
    "gui_web_2d_vulkan_simple_argb_height=2160\n" +
    "gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_chrome_argb_width=3840\n" +
    "gui_web_2d_vulkan_chrome_argb_height=2160\n" +
    "gui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_electron_argb_width=3840\n" +
    "gui_web_2d_vulkan_electron_argb_height=2160\n" +
    "gui_web_2d_vulkan_electron_argb_nonblank_pixel_count=42\n" +
    "EOF\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-fail/out GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-fail/gui.env GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/test-linux-vulkan-render-log-fail/gui.env LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0 sh scripts/check/check-linux-vulkan-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read fail-closed evidence")
val evidence = file_read("build/test-linux-vulkan-render-log-fail/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(evidence).to_contain("electron-browser-backing-fail")
expect(evidence).to_contain("browser-backing-fail")
```

</details>

#### uses focused browser backing evidence with direct-run pixel evidence

- Create direct-run pixel evidence and a separate focused browser-backing env
   - Expected: code equals `0`
- Assert the Linux compare reason uses focused backing statuses
   - Expected: evidence does not contain `chrome-browser-backing-missing`
   - Expected: evidence does not contain `chrome-browser-backing-fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create direct-run pixel evidence and a separate focused browser-backing env")
val command = "rm -rf build/test-linux-vulkan-render-log-focused-backing && mkdir -p build/test-linux-vulkan-render-log-focused-backing && cat > build/test-linux-vulkan-render-log-focused-backing/run.env <<'EOF'\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "EOF\n" +
    "cat > build/test-linux-vulkan-render-log-focused-backing/browser.env <<'EOF'\n" +
    "gui_web_2d_vulkan_browser_backing_status=fail\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=fail\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "EOF\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-focused-backing/out GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-focused-backing/run.env GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/test-linux-vulkan-render-log-focused-backing/browser.env LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0 sh scripts/check/check-linux-vulkan-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the Linux compare reason uses focused backing statuses")
val evidence = file_read("build/test-linux-vulkan-render-log-focused-backing/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(evidence).to_contain("linux_vulkan_render_log_compare_browser_backing_env=build/test-linux-vulkan-render-log-focused-backing/browser.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_pairwise_status=pass")
expect(evidence).to_contain("electron-browser-backing-fail")
expect(evidence).to_contain("browser-backing-fail")
expect(evidence.contains("chrome-browser-backing-missing")).to_equal(false)
expect(evidence.contains("chrome-browser-backing-fail")).to_equal(false)
```

</details>

#### prefers current main browser-backing evidence over stale focused evidence

- Create a current main browser-backing env and a stale separate focused env
   - Expected: code equals `0`
- Assert the current main browser-backing env wins over stale focused evidence
   - Expected: evidence does not contain `electron-browser-backing-fail`
   - Expected: evidence does not contain `browser-backing-fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a current main browser-backing env and a stale separate focused env")
val command = "rm -rf build/test-linux-vulkan-render-log-main-browser-backing && mkdir -p build/test-linux-vulkan-render-log-main-browser-backing && cat > build/test-linux-vulkan-render-log-main-browser-backing/main.env <<'EOF'\n" +
    "gui_web_2d_vulkan_mode=--browser-backing\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "EOF\n" +
    "cat > build/test-linux-vulkan-render-log-main-browser-backing/stale.env <<'EOF'\n" +
    "gui_web_2d_vulkan_browser_backing_status=fail\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=fail\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "EOF\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-main-browser-backing/out GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-main-browser-backing/main.env GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/test-linux-vulkan-render-log-main-browser-backing/stale.env LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0 sh scripts/check/check-linux-vulkan-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the current main browser-backing env wins over stale focused evidence")
val evidence = file_read("build/test-linux-vulkan-render-log-main-browser-backing/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_browser_backing_env=build/test-linux-vulkan-render-log-main-browser-backing/main.env")
expect(evidence.contains("electron-browser-backing-fail")).to_equal(false)
expect(evidence.contains("browser-backing-fail")).to_equal(false)
```

</details>

#### rejects Linux Vulkan pairwise rows without comparable nonblank ARGB viewports

- Create pairwise pass evidence with blank Chrome pixels and a mismatched Electron viewport
   - Expected: code equals `0`
- Assert the Linux gate rejects blank and mismatched ARGB evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create pairwise pass evidence with blank Chrome pixels and a mismatched Electron viewport")
val command = "rm -rf build/test-linux-vulkan-render-log-argb-geometry && mkdir -p build/test-linux-vulkan-render-log-argb-geometry && cat > build/test-linux-vulkan-render-log-argb-geometry/gui.env <<'EOF'\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_simple_argb_width=3840\n" +
    "gui_web_2d_vulkan_simple_argb_height=2160\n" +
    "gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_chrome_argb_width=3840\n" +
    "gui_web_2d_vulkan_chrome_argb_height=2160\n" +
    "gui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=0\n" +
    "gui_web_2d_vulkan_electron_argb_width=1920\n" +
    "gui_web_2d_vulkan_electron_argb_height=1080\n" +
    "gui_web_2d_vulkan_electron_argb_nonblank_pixel_count=42\n" +
    "EOF\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-argb-geometry/out GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-argb-geometry/gui.env GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/test-linux-vulkan-render-log-argb-geometry/gui.env LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0 sh scripts/check/check-linux-vulkan-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the Linux gate rejects blank and mismatched ARGB evidence")
val evidence = file_read("build/test-linux-vulkan-render-log-argb-geometry/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(evidence).to_contain("chrome-argb-blank")
expect(evidence).to_contain("argb-viewport-mismatch")
val chrome_log = file_read("build/test-linux-vulkan-render-log-argb-geometry/out/chrome.srl.env")
expect(chrome_log).to_contain("simple_render_log_nonblank_status=fail")
```

</details>

#### preserves RenderDoc failure reasons in Linux source logs

- Create passing pixel evidence with a Chrome RenderDoc crash reason
   - Expected: code equals `0`
- Assert Chrome RenderDoc failure fails the rollup and is normalized


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create passing pixel evidence with a Chrome RenderDoc crash reason")
val command = "rm -rf build/test-linux-vulkan-render-log-rdoc-reason && mkdir -p build/test-linux-vulkan-render-log-rdoc-reason/rdoc/simple build/test-linux-vulkan-render-log-rdoc-reason/rdoc/html build/test-linux-vulkan-render-log-rdoc-reason/rdoc/electron && cat > build/test-linux-vulkan-render-log-rdoc-reason/gui.env <<'EOF'\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_simple_argb_width=3840\n" +
    "gui_web_2d_vulkan_simple_argb_height=2160\n" +
    "gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_chrome_argb_width=3840\n" +
    "gui_web_2d_vulkan_chrome_argb_height=2160\n" +
    "gui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_electron_argb_width=3840\n" +
    "gui_web_2d_vulkan_electron_argb_height=2160\n" +
    "gui_web_2d_vulkan_electron_argb_nonblank_pixel_count=42\n" +
    "EOF\n" +
    "printf 'rdoc_simple_gate_status=pass\\nrdoc_simple_gate_reason=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\n' > build/test-linux-vulkan-render-log-rdoc-reason/rdoc/simple/evidence.env\n" +
    "printf 'rdoc_external_host_capture_gate_status=fail\\nrdoc_external_host_gate_reason=gate-command-failed\\nrdoc_external_host_capture_reason_raw=chromium-gpu-process-crashed-under-renderdoc\\nrdoc_capture_status=fail\\nrdoc_capture_reason=chromium-gpu-process-crashed-under-renderdoc\\n' > build/test-linux-vulkan-render-log-rdoc-reason/rdoc/html/evidence.env\n" +
    "printf 'rdoc_electron_html_gate_status=pass\\nrdoc_electron_html_gate_reason=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\n' > build/test-linux-vulkan-render-log-rdoc-reason/rdoc/electron/evidence.env\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-rdoc-reason/out GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-rdoc-reason/gui.env RDOC_SIMPLE_EVIDENCE_ENV=build/test-linux-vulkan-render-log-rdoc-reason/rdoc/simple/evidence.env RDOC_HTML_EVIDENCE_ENV=build/test-linux-vulkan-render-log-rdoc-reason/rdoc/html/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-linux-vulkan-render-log-rdoc-reason/rdoc/electron/evidence.env sh scripts/check/check-linux-vulkan-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert Chrome RenderDoc failure fails the rollup and is normalized")
val evidence = file_read("build/test-linux-vulkan-render-log-rdoc-reason/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(evidence).to_contain("linux_vulkan_render_log_compare_reason=renderdoc-chrome-fail")
expect(evidence).to_contain("linux_vulkan_render_log_compare_require_renderdoc=1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_status=fail")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_reason=gate-command-failed")
val chrome_log = file_read("build/test-linux-vulkan-render-log-rdoc-reason/out/chrome.srl.env")
expect(chrome_log).to_contain("simple_render_log_status=fail")
expect(chrome_log).to_contain("simple_render_log_reason=gate-command-failed")
```

</details>

#### allows diagnostic partial logs only when RenderDoc strictness is disabled

- Create passing pixel evidence with a Chrome RenderDoc failure and disable strict RenderDoc
   - Expected: code equals `0`
- Assert diagnostic mode preserves the failed RenderDoc row without failing compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create passing pixel evidence with a Chrome RenderDoc failure and disable strict RenderDoc")
val command = "rm -rf build/test-linux-vulkan-render-log-rdoc-diagnostic && mkdir -p build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/simple build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/html build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/electron && cat > build/test-linux-vulkan-render-log-rdoc-diagnostic/gui.env <<'EOF'\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_simple_argb_width=3840\n" +
    "gui_web_2d_vulkan_simple_argb_height=2160\n" +
    "gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_chrome_argb_width=3840\n" +
    "gui_web_2d_vulkan_chrome_argb_height=2160\n" +
    "gui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_electron_argb_width=3840\n" +
    "gui_web_2d_vulkan_electron_argb_height=2160\n" +
    "gui_web_2d_vulkan_electron_argb_nonblank_pixel_count=42\n" +
    "EOF\n" +
    "printf 'rdoc_simple_gate_status=pass\\nrdoc_simple_gate_reason=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\n' > build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/simple/evidence.env\n" +
    "printf 'rdoc_external_host_capture_gate_status=fail\\nrdoc_external_host_gate_reason=gate-command-failed\\nrdoc_capture_status=fail\\n' > build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/html/evidence.env\n" +
    "printf 'rdoc_electron_html_gate_status=pass\\nrdoc_electron_html_gate_reason=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\n' > build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/electron/evidence.env\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-rdoc-diagnostic/out GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-rdoc-diagnostic/gui.env RDOC_SIMPLE_EVIDENCE_ENV=build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/simple/evidence.env RDOC_HTML_EVIDENCE_ENV=build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/html/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-linux-vulkan-render-log-rdoc-diagnostic/rdoc/electron/evidence.env LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0 sh scripts/check/check-linux-vulkan-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert diagnostic mode preserves the failed RenderDoc row without failing compare")
val evidence = file_read("build/test-linux-vulkan-render-log-rdoc-diagnostic/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_reason=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_require_renderdoc=0")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_status=fail")
```

</details>

#### defaults RenderDoc inputs to focused current capture evidence

- Read the Linux render-log wrapper defaults
- Assert default RenderDoc env paths use focused evidence rows
   - Expected: script does not contain `build/renderdoc/canonical-probe/simple/evidence.env`
   - Expected: script does not contain `build/renderdoc/canonical-probe/html/evidence.env`
   - Expected: script does not contain `build/renderdoc/canonical-probe/electron-html/evidence.env`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the Linux render-log wrapper defaults")
val script = file_read("scripts/check/check-linux-vulkan-render-log-compare.shs")

step("Assert default RenderDoc env paths use focused evidence rows")
expect(script).to_contain("RDOC_SIMPLE_EVIDENCE_ENV")
expect(script).to_contain("build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env")
expect(script).to_contain("RDOC_HTML_EVIDENCE_ENV")
expect(script).to_contain("build/renderdoc/chrome-display-helper/evidence.env")
expect(script).to_contain("RDOC_ELECTRON_HTML_EVIDENCE_ENV")
expect(script).to_contain("build/renderdoc/electron-display-helper/electron-html/evidence.env")
expect(script.contains("build/renderdoc/canonical-probe/simple/evidence.env")).to_equal(false)
expect(script.contains("build/renderdoc/canonical-probe/html/evidence.env")).to_equal(false)
expect(script.contains("build/renderdoc/canonical-probe/electron-html/evidence.env")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
