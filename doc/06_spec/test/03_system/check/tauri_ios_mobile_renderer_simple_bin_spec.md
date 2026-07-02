# Tauri iOS Mobile Renderer Simple Binary Contract

> The iOS mobile renderer wrapper produces Metal/WKWebView renderer evidence and MDI proof diagnostics. It must not hide host-side Simple regressions behind the Rust bootstrap seed, while preserving the existing non-Darwin unavailable path for hosts without iOS tooling.

<!-- sdn-diagram:id=tauri_ios_mobile_renderer_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_ios_mobile_renderer_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_ios_mobile_renderer_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_ios_mobile_renderer_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri iOS Mobile Renderer Simple Binary Contract

The iOS mobile renderer wrapper produces Metal/WKWebView renderer evidence and MDI proof diagnostics. It must not hide host-side Simple regressions behind the Rust bootstrap seed, while preserving the existing non-Darwin unavailable path for hosts without iOS tooling.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/tauri_ios_mobile_renderer_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The iOS mobile renderer wrapper produces Metal/WKWebView renderer evidence and
MDI proof diagnostics. It must not hide host-side Simple regressions behind the
Rust bootstrap seed, while preserving the existing non-Darwin unavailable path
for hosts without iOS tooling.

## Requirements

**Requirements:** N/A

- REQ-TAURI-IOS-RENDERER-BIN-001: Default host Simple binary selection is
  self-hosted only.
- REQ-TAURI-IOS-RENDERER-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before iOS simulator, Tauri, npm, cargo, or validator
  work.
- REQ-TAURI-IOS-RENDERER-BIN-003: Normalized diagnostics record selected Simple
  binary, source, and status fields.
- REQ-TAURI-IOS-RENDERER-BIN-004: Tests can isolate output through a
  `BUILD_DIR` override.

## Plan

**Plan:** doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and diagnostic fields.
3. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
4. Confirm stdout shows `simple-bin-forbidden`.
5. Confirm iOS renderer logs are not created on the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates explicit Rust seed overrides before the platform gate, but
keeps ordinary missing non-seed launchers on the existing host-readiness path.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_ios_mobile_renderer_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### Tauri iOS mobile renderer Simple binary contract

#### selects self hosted Simple and records launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-tauri-ios-mobile-renderer-evidence.shs")
expect(script).to_contain("BUILD_DIR=")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("/release/*/simple")
expect(script).to_contain("/bin/release/*/simple")
expect(script).to_contain("/build/bootstrap/stage3/simple")
expect(script).to_contain("/bin/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("tauri_ios_mobile_renderer_simple_bin=")
expect(script).to_contain("tauri_ios_mobile_renderer_simple_bin_source=")
expect(script).to_contain("tauri_ios_mobile_renderer_simple_bin_status=")
```

</details>

#### launches the bundled MDI smoke entry for live renderer proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-tauri-ios-mobile-renderer-evidence.shs")
expect(script).to_contain("SMOKE_SOURCE=\"$ROOT_DIR/examples/06_io/ui/tauri_mobile_mdi_smoke.spl\"")
expect(script).to_contain("printf 'mdi-smoke\\n' > \"$TAURI_DIR/src-tauri/mobile_probe_entry.txt\"")
expect(script).to_contain("cp \"$SMOKE_SOURCE\" \"$TAURI_DIR/src-tauri/mobile_entry_source.spl\"")
expect(script).to_contain("rm -f \"$TAURI_DIR/src-tauri/mobile_mdi_proof_url.txt\"")
expect(script).to_contain("SIMPLE_TAURI_MOBILE_PROBE_ENTRY=mdi-smoke")
expect(script).to_contain("SIMPLE_TAURI_MDI_PROOF_PATH=\"$MDI_PROOF_JSON\"")
expect(script).to_contain("xcrun simctl terminate \"$SIM_UDID\" com.simple.ui")
expect(script).to_contain("xcrun simctl uninstall \"$SIM_UDID\" com.simple.ui")
expect(script).to_contain("echo \"ios_mdi_proof_status=$ios_mdi_proof_status\"")
expect(script).to_contain("echo \"ios_mdi_event_status=$ios_mdi_event_status\"")
expect(script).to_contain("echo \"ios_mdi_capture_status=$ios_mdi_capture_status\"")
expect(script).to_contain("echo \"ios_mdi_performance_status=$ios_mdi_performance_status\"")
expect(script).to_contain("echo \"ios_mdi_animation_status=$ios_mdi_animation_status\"")
```

</details>

#### rejects explicit Rust seed before iOS renderer platform work

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-mobile-renderer-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out sh scripts/check/check-tauri-ios-mobile-renderer-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("status=fail")
expect(output).to_contain("reason=simple-bin-forbidden")
expect(output).to_contain("tauri_ios_mobile_renderer_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("tauri_ios_mobile_renderer_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("tauri_ios_mobile_renderer_simple_bin_status=forbidden")
expect(output).to_contain("ios_screenshot_actual_size_bytes=")
expect(output).to_contain("ios_screenshot_file_status=unavailable")
expect(output).to_contain("ios_screenshot_file_reason=not-run")
expect(output).to_contain("ios_screenshot_artifact_status=unavailable")
expect(output).to_contain("ios_screenshot_pixel_diversity_status=unavailable")
expect(output).to_contain("ios_render_log_status=fail")
expect(output).to_contain("ios_mdi_proof_status=fail")

val (_dev_out, _dev_err, dev_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/ios_renderer_tauri_dev.log"])
expect(dev_code).to_equal(0)
val (_stream_out, _stream_err, stream_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/ios_renderer_log_stream.txt"])
expect(stream_code).to_equal(0)
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

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md](doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md](doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md)


</details>
