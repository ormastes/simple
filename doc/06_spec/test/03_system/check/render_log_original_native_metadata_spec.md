# Render-Log Original Native Metadata Contract

> Validates the shared `simple-render-log-v1` metadata that identifies the original native capture or debugger log behind each normalized Simple render log. This is the host-independent contract for comparing Linux RenderDoc, macOS Metal/Xcode GPU capture, Windows D3D12/PIX, generic GPU debugger logs, and browser GPU metadata without inventing unrelated platform key names.

<!-- sdn-diagram:id=render_log_original_native_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=render_log_original_native_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

render_log_original_native_metadata_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=render_log_original_native_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render-Log Original Native Metadata Contract

Validates the shared `simple-render-log-v1` metadata that identifies the original native capture or debugger log behind each normalized Simple render log. This is the host-independent contract for comparing Linux RenderDoc, macOS Metal/Xcode GPU capture, Windows D3D12/PIX, generic GPU debugger logs, and browser GPU metadata without inventing unrelated platform key names.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/render_log_original_native_metadata_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the shared `simple-render-log-v1` metadata that identifies the
original native capture or debugger log behind each normalized Simple render
log. This is the host-independent contract for comparing Linux RenderDoc,
macOS Metal/Xcode GPU capture, Windows D3D12/PIX, generic GPU debugger logs,
and browser GPU metadata without inventing unrelated platform key names.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/render_log_original_native_metadata_spec.spl --native
```

## Operator Flow

1. Run the platform compare wrapper for Linux Vulkan, macOS Metal, or Windows
   D3D12.
2. Open the generated `*.srl.env` files in that wrapper's build directory.
3. Read `simple_render_log_original_capture_tool`,
   `simple_render_log_original_native_log_format`, and
   `simple_render_log_original_native_log_source` before comparing logs across
   platforms.
4. Treat the original metadata as provenance only. Passing evidence still
   requires the platform-specific compare status, pairwise status, and native
   capture/debugger proof keys.

## Evidence Contract

Every normalized source log keeps the existing fields:

- `simple_render_log_format=simple-render-log-v1`
- `simple_render_log_capture_tool`
- `simple_render_log_source_env`
- `simple_render_log_native_info`

It also emits explicit original-native fields:

- `simple_render_log_original_capture_tool`
- `simple_render_log_original_native_log_format`
- `simple_render_log_original_native_log_source`

The format value is derived conservatively from artifact magic first, then from
the capture tool:

- `RDOC` -> `renderdoc-rdc`
- `XCODE-GPUTRACE` -> `xcode-gputrace`
- `PIX` -> `pix-capture`
- tool containing `gpu-debugger` -> `gpu-debugger-log`
- `browser-gpu-metadata` -> `browser-gpu-metadata`
- tool containing `renderdoc` without RDOC magic -> `renderdoc-diagnostic`

## Completion Boundaries

This spec does not run RenderDoc, Xcode GPU capture, PIX, Chrome, Electron, or
the Simple renderer. It only proves that the shared normalization layer records
enough provenance for later platform hosts to compare native logs in one
schema. Do not treat fixture rows from this spec as render evidence.

## Platform Interpretation

For Linux Vulkan, `renderdoc-rdc` means the normalized row came from a real
RenderDoc capture artifact whose magic was `RDOC`. `renderdoc-diagnostic` means
the row was produced by a RenderDoc-oriented probe, but it did not prove a
valid `.rdc` artifact. The Linux platform matrix must still fail until Simple,
Chrome, and Electron RenderDoc statuses pass.

For macOS Metal, `xcode-gputrace` identifies Xcode GPU Frame Capture evidence.
It supplements Metal readback, framebuffer readback, and browser Metal backing;
it does not replace those checks. A macOS row with only browser metadata remains
incomplete for native Metal capture proof.

For Windows D3D12, `pix-capture` identifies PIX evidence and
`gpu-debugger-log` identifies an equivalent GPU debugger log. Strict Windows
completion requires the row to prove D3D12 readback, browser D3D12 backing,
pairwise pixels, PIX, and GPU debugger status when required by the platform
matrix.

For Chrome/Electron browser rows, `browser-gpu-metadata` is intentionally not a
debugger format. It preserves ANGLE/Skia/backend provenance for comparison, but
cannot satisfy a native debugger or `.rdc` capture gate by itself.

## Failure Semantics

The original-native fields must be present even on failing rows. A failure row
with `simple_render_log_original_native_log_format=renderdoc-diagnostic` is more
actionable than a blank row because the next operator knows to inspect RenderDoc
injection, target selection, or capture timing. A blank or missing original
format is a schema regression, not a platform limitation.

The normalized schema intentionally keeps free-form details in
`simple_render_log_native_info`. Platform wrappers may append sidecar fields for
new debugger tools, but must keep the three original-native keys stable so
aggregate comparison tools can remain platform-neutral.

## Test Matrix

1. A Linux RenderDoc source log with `RDOC` magic records `renderdoc-rdc`.
2. Native logs with Xcode GPU capture, PIX, and generic GPU debugger metadata
   record distinct original-native formats.
3. Browser GPU metadata rows remain comparable without pretending to be native
   debugger captures.

## Scenarios

### Render-log original native metadata

#### records RenderDoc RDC provenance for Linux source logs

- Generate a normalized Linux RenderDoc source log
   - Expected: code equals `0`
- Assert original RenderDoc metadata is explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate a normalized Linux RenderDoc source log")
val command = "rm -rf build/test-render-log-original-native-linux && mkdir -p build/test-render-log-original-native-linux && " +
    "printf 'gui_web_2d_vulkan_chrome_argb_width=64\\ngui_web_2d_vulkan_chrome_argb_height=32\\ngui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=9\\ngui_web_2d_vulkan_chrome_argb_checksum=123\\ngui_web_2d_vulkan_chrome_argb_backend=vulkan\\n' > build/test-render-log-original-native-linux/native.env && " +
    "printf 'rdoc_capture_magic=RDOC\\n' > build/test-render-log-original-native-linux/source.env && " +
    ". scripts/lib/render-log-common.shs && render_log_write_source_log build/test-render-log-original-native-linux/chrome.srl.env chrome renderdoc build/test-render-log-original-native-linux/source.env build/test-render-log-original-native-linux/native.env pass frame.rdc RDOC 'browser-backing=pass' pass"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert original RenderDoc metadata is explicit")
val log = file_read("build/test-render-log-original-native-linux/chrome.srl.env")
expect(log).to_contain("simple_render_log_format=simple-render-log-v1")
expect(log).to_contain("simple_render_log_capture_tool=renderdoc")
expect(log).to_contain("simple_render_log_original_capture_tool=renderdoc")
expect(log).to_contain("simple_render_log_original_native_log_format=renderdoc-rdc")
expect(log).to_contain("simple_render_log_original_native_log_source=build/test-render-log-original-native-linux/source.env")
expect(log).to_contain("simple_render_log_artifact_magic=RDOC")
```

</details>

#### records Xcode GPU capture PIX and GPU debugger provenance for native logs

- Generate normalized native logs for Metal, PIX, and generic GPU debugger inputs
   - Expected: code equals `0`
- Assert platform-native formats remain distinguishable


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate normalized native logs for Metal, PIX, and generic GPU debugger inputs")
val command = "rm -rf build/test-render-log-original-native-platforms && mkdir -p build/test-render-log-original-native-platforms && " +
    ". scripts/lib/render-log-common.shs && " +
    "render_log_write_native_log build/test-render-log-original-native-platforms/metal.srl.env macos metal simple xcode-gpu-frame-capture build/test-render-log-original-native-platforms/metal.env pass metal 64 32 9 frame.gputrace XCODE-GPUTRACE 111 'capture=pass' && " +
    "render_log_write_native_log build/test-render-log-original-native-platforms/pix.srl.env windows d3d12 simple pix-or-gpu-debugger build/test-render-log-original-native-platforms/pix.env pass d3d12 64 32 9 frame.wpix PIX 222 'pix=pass' && " +
    "render_log_write_native_log build/test-render-log-original-native-platforms/gpu-debugger.srl.env windows d3d12 simple vendor-gpu-debugger build/test-render-log-original-native-platforms/gpu-debugger.env pass d3d12 64 32 9 frame.json '' 333 'gpu-debugger=pass'"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert platform-native formats remain distinguishable")
val metal = file_read("build/test-render-log-original-native-platforms/metal.srl.env")
val pix = file_read("build/test-render-log-original-native-platforms/pix.srl.env")
val gpu_debugger = file_read("build/test-render-log-original-native-platforms/gpu-debugger.srl.env")
expect(metal).to_contain("simple_render_log_original_native_log_format=xcode-gputrace")
expect(metal).to_contain("simple_render_log_original_capture_tool=xcode-gpu-frame-capture")
expect(pix).to_contain("simple_render_log_original_native_log_format=pix-capture")
expect(pix).to_contain("simple_render_log_original_capture_tool=pix-or-gpu-debugger")
expect(gpu_debugger).to_contain("simple_render_log_original_native_log_format=gpu-debugger-log")
expect(gpu_debugger).to_contain("simple_render_log_original_capture_tool=vendor-gpu-debugger")
```

</details>

#### records browser GPU metadata as metadata instead of debugger proof

- Generate a normalized browser metadata source log without native artifact magic
   - Expected: code equals `0`
- Assert browser metadata is not mislabeled as a capture artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate a normalized browser metadata source log without native artifact magic")
val command = "rm -rf build/test-render-log-original-native-browser && mkdir -p build/test-render-log-original-native-browser && " +
    "printf 'gui_web_2d_vulkan_electron_argb_width=64\\ngui_web_2d_vulkan_electron_argb_height=32\\ngui_web_2d_vulkan_electron_argb_nonblank_pixel_count=9\\ngui_web_2d_vulkan_electron_argb_checksum=444\\ngui_web_2d_vulkan_electron_argb_backend=vulkan\\n' > build/test-render-log-original-native-browser/native.env && " +
    "printf 'browser_status=pass\\n' > build/test-render-log-original-native-browser/source.env && " +
    ". scripts/lib/render-log-common.shs && render_log_write_source_log build/test-render-log-original-native-browser/electron.srl.env electron browser-gpu-metadata build/test-render-log-original-native-browser/source.env build/test-render-log-original-native-browser/native.env pass '' '' 'browser-backing=pass' pass"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert browser metadata is not mislabeled as a capture artifact")
val log = file_read("build/test-render-log-original-native-browser/electron.srl.env")
expect(log).to_contain("simple_render_log_original_capture_tool=browser-gpu-metadata")
expect(log).to_contain("simple_render_log_original_native_log_format=browser-gpu-metadata")
expect(log).to_contain("simple_render_log_original_native_log_source=build/test-render-log-original-native-browser/source.env")
expect(log).to_contain("simple_render_log_artifact_magic=")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
