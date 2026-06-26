# Tauri iOS render-log validator

> Validates the iOS mobile render-log proof used by the Tauri renderer evidence wrappers. A pass must include a Tauri render marker, an iOS/Tauri webview context marker, a Metal context marker, and no failure markers.

<!-- sdn-diagram:id=tauri_ios_render_log_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_ios_render_log_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_ios_render_log_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_ios_render_log_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri iOS render-log validator

Validates the iOS mobile render-log proof used by the Tauri renderer evidence wrappers. A pass must include a Tauri render marker, an iOS/Tauri webview context marker, a Metal context marker, and no failure markers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/tauri_ios_render_log_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the iOS mobile render-log proof used by the Tauri renderer evidence
wrappers. A pass must include a Tauri render marker, an iOS/Tauri webview
context marker, a Metal context marker, and no failure markers.

**Plan:** doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_ios_render_log_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Complete iOS Tauri/WKWebView/Metal logs validate and emit normalized rows.
- Render-only or generic Metal-only logs fail closed.
- Failure markers such as eval failures fail closed even when render and Metal
  markers are present.
- The iOS renderer wrapper, mobile aggregate, and Tauri shell source are wired
  to the validator contract.

## Scenarios

### Tauri iOS render-log validator

#### accepts complete Tauri WKWebView Metal render-log proof

- Inspect normalized iOS render-log rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect normalized iOS render-log rows")
expect(evidence).to_contain("ios_render_log_validation_status=pass")
expect(evidence).to_contain("ios_render_log_validation_reason=pass")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_failure_marker_status=pass")
```

</details>

#### rejects generic Metal text without iOS Tauri webview context

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-generic-metal"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=347702\\nMetal renderer ready\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-tauri-wkwebview-context-missing")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("ios_render_log_tauri_context_status=fail")
```

</details>

#### rejects missing render or Metal markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-missing-markers"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/no-render.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/no-render.log > " + root + "/no-render.env; " +
    "printf '[tauri-shell] ios renderer context: backend=WKWebView\\n[tauri-shell] render, html_len=347702\\n' > " + root + "/no-metal.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/no-metal.log > " + root + "/no-metal.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val no_render = file_read(root + "/no-render.env")
val no_metal = file_read(root + "/no-metal.env")
expect(no_render).to_contain("ios_render_log_validation_reason=ios-render-log-marker-missing")
expect(no_render).to_contain("ios_render_log_marker_status=fail")
expect(no_metal).to_contain("ios_render_log_validation_reason=ios-metal-log-marker-missing")
expect(no_metal).to_contain("ios_render_log_metal_marker_status=fail")
```

</details>

#### rejects render-log failure markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-failure"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n[tauri-shell] eval FAIL: rejected\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-render-log-failure-marker")
expect(evidence).to_contain("ios_render_log_failure_marker_status=fail")
```

</details>

#### keeps the iOS renderer wrappers and Tauri shell wired to the validator

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = file_read("scripts/check/check-tauri-ios-mobile-renderer-evidence.shs")
val aggregate = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
val tauri = file_read("tools/tauri-shell/src-tauri/src/lib.rs")
expect(direct).to_contain("validate-tauri-ios-render-log-proof.js")
expect(direct).to_contain("ios_render_log.validation.env")
expect(aggregate).to_contain("TAURI_MOBILE_RENDERER_IOS_RENDER_LOG_VALIDATOR")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status")
expect(aggregate).to_contain("ios-tauri-wkwebview-context-missing")
expect(tauri).to_contain("ios renderer context: backend=WKWebView")
expect(tauri).to_contain("metal_layer=CAMetalLayer")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
