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
| 14 | 14 | 0 | 0 |

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
- The Tauri render marker must include a clean positive decimal `html_len`.
- Render-only or generic Metal-only logs fail closed.
- Bare `WKWebView` text is not enough; the context marker must be tied to the
  Tauri shell or the mobile MDI probe source.
- Metal evidence must be tied to the Tauri iOS WKWebView context line; generic
  Metal log text elsewhere is not enough.
- The iOS context line must include both `metal_expected=true` and
  `metal_layer=CAMetalLayer`; a generic Metal expectation flag is not enough.
- The CAMetalLayer context binding alone is not enough; a separate Metal
  runtime readiness marker must be present in the same coherent source log.
- Render, WKWebView, and CAMetalLayer markers must be coherent within one
  source log; markers split across unrelated log files fail closed.
- Explicitly requested iOS log source paths must exist; a valid companion log
  cannot hide a missing render-log source artifact.
- Explicitly requested iOS log source paths must be nonempty; a valid
  companion log cannot hide an empty render-log source artifact.
- Failure markers such as eval failures fail closed even when render and Metal
  markers are present.
- The iOS renderer wrapper keeps render-log, Metal, MDI event/capture,
  performance, input-to-paint, and animation diagnostic rows on early
  unavailable/fail exits.
- The iOS renderer wrapper persists render-log and MDI validator output and
  re-emits validator-derived success rows instead of fixed pass strings.
- The iOS renderer wrapper, mobile aggregate, and Tauri shell source are wired
  to the validator contract.

## Scenarios

### Tauri iOS render-log validator

#### accepts complete Tauri WKWebView Metal render-log proof

- Inspect normalized iOS render-log rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
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
expect(evidence).to_contain("ios_render_log_requested_source_count=1")
expect(evidence).to_contain("ios_render_log_source_count=1")
expect(evidence).to_contain("ios_render_log_missing_source_count=0")
expect(evidence).to_contain("ios_render_log_empty_source_count=0")
expect(evidence).to_contain("ios_render_log_source_coherence_status=pass")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_html_len=347702")
expect(evidence).to_contain("ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
expect(evidence).to_contain("ios_render_log_failure_marker_status=pass")
```

</details>

#### rejects malformed iOS render html length markers

- Confirm iOS render html_len must be a clean positive decimal row


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-html-len"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702px\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/suffix.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/suffix.log > " + root + "/suffix.env; " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=0\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/zero.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/zero.log > " + root + "/zero.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val suffix = file_read(root + "/suffix.env")
val zero = file_read(root + "/zero.env")
step("Confirm iOS render html_len must be a clean positive decimal row")
expect(suffix).to_contain("ios_render_log_validation_status=fail")
expect(suffix).to_contain("ios_render_log_validation_reason=ios-render-log-html-len-malformed")
expect(suffix).to_contain("ios_render_log_marker_status=fail")
expect(suffix).to_contain("ios_render_log_html_len=")
expect(zero).to_contain("ios_render_log_validation_status=fail")
expect(zero).to_contain("ios_render_log_validation_reason=ios-render-log-html-len-malformed")
expect(zero).to_contain("ios_render_log_marker_status=fail")
expect(zero).to_contain("ios_render_log_html_len=")
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

#### rejects generic Metal text that is not tied to the iOS context line

- Confirm iOS Metal proof is bound to the WKWebView context row


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-metal-context"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm iOS Metal proof is bound to the WKWebView context row")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-metal-context-missing")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=fail")
```

</details>

#### rejects CAMetalLayer context without a Metal runtime readiness marker

- Confirm CAMetalLayer binding does not replace a runtime Metal marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-context-only-metal"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm CAMetalLayer binding does not replace a runtime Metal marker")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-metal-log-marker-missing")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=fail")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
expect(evidence).to_contain("ios_render_log_source_coherence_status=fail")
```

</details>

#### rejects pass markers split across unrelated log sources

- Confirm iOS render and Metal proof must be coherent within one source


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-source-mismatch"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=347702\\n' > " + root + "/render.log && " +
    "printf '[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/metal.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/render.log " + root + "/metal.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm iOS render and Metal proof must be coherent within one source")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-render-log-source-mismatch")
expect(evidence).to_contain("ios_render_log_source_count=2")
expect(evidence).to_contain("ios_render_log_source_coherence_status=fail")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
```

</details>

#### rejects missing requested iOS log source paths

- Confirm valid iOS render evidence cannot hide a missing requested source


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-missing-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log " + root + "/missing.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm valid iOS render evidence cannot hide a missing requested source")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-render-log-source-missing")
expect(evidence).to_contain("ios_render_log_requested_source_count=2")
expect(evidence).to_contain("ios_render_log_source_count=1")
expect(evidence).to_contain("ios_render_log_missing_source_count=1")
expect(evidence).to_contain("ios_render_log_empty_source_count=0")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
```

</details>

#### rejects empty requested iOS log source paths

- Confirm valid iOS render evidence cannot hide an empty requested source


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-empty-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    ": > " + root + "/empty.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log " + root + "/empty.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm valid iOS render evidence cannot hide an empty requested source")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-render-log-source-empty")
expect(evidence).to_contain("ios_render_log_requested_source_count=2")
expect(evidence).to_contain("ios_render_log_source_count=1")
expect(evidence).to_contain("ios_render_log_missing_source_count=0")
expect(evidence).to_contain("ios_render_log_empty_source_count=1")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
```

</details>

#### rejects iOS context lines without a CAMetalLayer binding

- Confirm expected-Metal flags need the native CAMetalLayer binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-metal-layer"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm expected-Metal flags need the native CAMetalLayer binding")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-metal-context-missing")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=fail")
```

</details>

#### rejects bare WKWebView text that is not tied to Tauri shell context

- Confirm generic WebKit text does not satisfy the Tauri context contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-bare-wkwebview"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\nWKWebView allocation note from unrelated framework\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm generic WebKit text does not satisfy the Tauri context contract")
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

#### keeps iOS render-log and MDI diagnostics on early wrapper exits

- Confirm early iOS wrapper exits preserve normalized render-log and MDI diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-wrapper-early-exit"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "SIMPLE_BIN=" + root + "/missing-simple sh scripts/check/check-tauri-ios-mobile-renderer-evidence.shs > " + root + "/stdout.env 2> " + root + "/stderr.log; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/stdout.env")
step("Confirm early iOS wrapper exits preserve normalized render-log and MDI diagnostics")
expect(evidence).to_contain("ios_render_log_status=")
expect(evidence).to_contain("ios_mdi_proof_validation_env=")
expect(evidence).to_contain("ios_layout_status=")
expect(evidence).to_contain("ios_metal_log_status=")
expect(evidence).to_contain("ios_render_log_validation_status=")
expect(evidence).to_contain("ios_render_log_validation_reason=")
expect(evidence).to_contain("ios_render_log_requested_source_count=0")
expect(evidence).to_contain("ios_render_log_source_count=0")
expect(evidence).to_contain("ios_render_log_missing_source_count=0")
expect(evidence).to_contain("ios_render_log_empty_source_count=0")
expect(evidence).to_contain("ios_render_log_source_coherence_status=")
expect(evidence).to_contain("ios_render_log_marker_status=")
expect(evidence).to_contain("ios_render_log_html_len=")
expect(evidence).to_contain("ios_render_log_metal_marker_status=")
expect(evidence).to_contain("ios_render_log_tauri_context_status=")
expect(evidence).to_contain("ios_render_log_metal_context_status=")
expect(evidence).to_contain("ios_render_log_failure_marker_status=")
expect(evidence).to_contain("ios_mdi_proof_status=")
expect(evidence).to_contain("ios_mdi_failure_marker_status=")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_render_status=")
expect(evidence).to_contain("ios_mdi_event_status=")
expect(evidence).to_contain("ios_mdi_event_body_click_routed=")
expect(evidence).to_contain("ios_mdi_event_taskbar_labels_visible=")
expect(evidence).to_contain("ios_mdi_capture_status=")
expect(evidence).to_contain("ios_mdi_performance_status=")
expect(evidence).to_contain("ios_mdi_performance_now_delta_ms=")
expect(evidence).to_contain("ios_mdi_interaction_latency_status=")
expect(evidence).to_contain("ios_mdi_input_to_paint_ms=")
expect(evidence).to_contain("ios_mdi_animation_status=")
expect(evidence).to_contain("ios_mdi_animation_frame_count=")
expect(evidence).to_contain("ios_mdi_css_animation_probe=")
```

</details>

#### keeps the iOS renderer wrappers and Tauri shell wired to the validator

<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = file_read("scripts/check/check-tauri-ios-mobile-renderer-evidence.shs")
val aggregate = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
val tauri = file_read("tools/tauri-shell/src-tauri/src/lib.rs")
expect(direct).to_contain("validate-tauri-ios-render-log-proof.js")
expect(direct).to_contain("ios_render_log.validation.env")
expect(direct).to_contain("ios_mdi_proof.validation.env")
expect(direct).to_contain("emit_unavailable_ios_diagnostics")
expect(direct).to_contain("value_of ios_render_log_validation_status")
expect(direct).to_contain("ios_render_log_empty_source_count=$ios_render_log_empty_source_count")
expect(direct).to_contain("ios_render_log_source_coherence_status=$ios_render_log_source_coherence_status")
expect(direct).to_contain("ios_render_log_tauri_context_status=$ios_render_log_tauri_context_status")
expect(direct).to_contain("ios_render_log_metal_context_status=$ios_render_log_metal_context_status")
expect(direct).to_contain("value_of ios_mdi_proof_status")
expect(direct).to_contain("ios_mdi_animation_frame_count")
expect(direct).to_contain("ios_mdi_input_to_paint_ms")
expect(direct).to_contain("ios_mdi_interaction_latency_status")
expect(direct).to_contain("ios_mdi_failure_marker_status")
expect(direct).to_contain("ios_mdi_event_body_click_routed")
expect(direct).to_contain("ios_mdi_event_taskbar_labels_visible")
expect(aggregate).to_contain("TAURI_MOBILE_RENDERER_IOS_RENDER_LOG_VALIDATOR")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_requested_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_missing_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_empty_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_html_len")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_source_coherence_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_context_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_body_click_routed")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_taskbar_labels_visible")
expect(aggregate).to_contain("ios-tauri-wkwebview-context-missing")
expect(aggregate).to_contain("ios-metal-context-missing")
expect(aggregate).to_contain("ios-render-log-source-mismatch")
expect(aggregate).to_contain("ios-render-log-source-missing")
expect(aggregate).to_contain("ios-render-log-source-empty")
expect(tauri).to_contain("ios renderer context: backend=WKWebView")
expect(tauri).to_contain("metal_layer=CAMetalLayer")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
