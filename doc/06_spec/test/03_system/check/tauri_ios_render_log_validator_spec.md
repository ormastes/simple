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
| 21 | 21 | 0 | 0 |

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
- Implausibly high iOS render `html_len` values fail closed instead of
  counting as valid rendered-surface proof.
- Render-only or generic Metal-only logs fail closed.
- Bare `WKWebView` text is not enough; the context marker must be tied to the
  Tauri shell or the mobile MDI probe source.
- Metal evidence must be tied to the Tauri iOS WKWebView context line; generic
  Metal log text elsewhere is not enough.
- The iOS context line must include both `metal_expected=true` and
  `metal_layer=CAMetalLayer`; a generic Metal expectation flag is not enough.
- The CAMetalLayer context binding alone is not enough; a separate CAMetalLayer
  or native Metal runtime readiness marker must be present in the same coherent
  source log, and generic Metal readiness text is not enough.
- Passing validation emits the exact coherent iOS render-log source path and
  byte size so aggregate evidence can bind Metal-backed rendering to a real log
  artifact.
- Passing validation binds `html_len` to the coherent WKWebView/CAMetalLayer
  render-log source instead of an unrelated companion render marker.
- Fallback GPU markers such as SwiftShader, software rendering, or OpenGL
  renderer fallback text fail even when the log also contains WKWebView,
  CAMetalLayer, and Metal markers.
- Render, WKWebView, and CAMetalLayer markers must be coherent within one
  source log; markers split across unrelated log files fail closed.
- Explicitly requested iOS log source paths must exist; a valid companion log
  cannot hide a missing render-log source artifact.
- Explicitly requested iOS log source paths must be nonempty; a valid
  companion log cannot hide an empty render-log source artifact.
- Explicitly requested iOS log source paths must be regular files, not
  symlinks to other render-log artifacts.
- Explicitly requested iOS log source paths must not be hardlinked aliases of
  other render-log artifacts.
- Explicitly requested iOS log source paths must not be directories or other
  non-regular artifacts.
- Failure markers such as eval failures fail closed even when render and Metal
  markers are present.
- The iOS renderer wrapper keeps render-log, Metal, MDI event/capture,
  performance, input-to-paint, and animation diagnostic rows on early
  unavailable/fail exits.
- The iOS renderer wrapper preserves validator-derived failure rows on later
  fail diagnostics instead of masking them with generic duplicate keys.
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

Runnable source: 26 lines folded for reproduction.
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
expect(evidence).to_contain("ios_render_log_symlink_source_count=0")
expect(evidence).to_contain("ios_render_log_hardlink_source_count=0")
expect(evidence).to_contain("ios_render_log_source_coherence_status=pass")
expect(evidence).to_contain("ios_render_log_coherent_source_path=" + root + "/ios.log")
expect(evidence).to_contain("ios_render_log_coherent_source_size_bytes=223")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_html_len=347702")
expect(evidence).to_contain("ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("ios_render_log_fallback_marker_status=pass")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
expect(evidence).to_contain("ios_render_log_failure_marker_status=pass")
```

</details>

#### binds html length evidence to the coherent iOS Metal source

- Confirm html_len is emitted from the coherent WKWebView/CAMetalLayer source
   - Expected: evidence does not contain `ios_render_log_html_len=999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-coherent-html-len"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] render, html_len=999\\n' > " + root + "/render-only.log && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/render-only.log " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Confirm html_len is emitted from the coherent WKWebView/CAMetalLayer source")
expect(evidence).to_contain("ios_render_log_validation_status=pass")
expect(evidence).to_contain("ios_render_log_requested_source_count=2")
expect(evidence).to_contain("ios_render_log_source_count=2")
expect(evidence).to_contain("ios_render_log_source_coherence_status=pass")
expect(evidence).to_contain("ios_render_log_coherent_source_path=" + root + "/ios.log")
expect(evidence).to_contain("ios_render_log_html_len=347702")
expect(evidence.contains("ios_render_log_html_len=999")).to_equal(false)
```

</details>

#### rejects malformed iOS render html length markers

- Confirm iOS render html_len must be a clean positive decimal row
   - Expected: huge does not contain `ios_render_log_html_len=10000001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-html-len"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702px\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/suffix.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/suffix.log > " + root + "/suffix.env; " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=0\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/zero.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/zero.log > " + root + "/zero.env; " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=10000001\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/huge.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/huge.log > " + root + "/huge.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val suffix = file_read(root + "/suffix.env")
val zero = file_read(root + "/zero.env")
val huge = file_read(root + "/huge.env")
step("Confirm iOS render html_len must be a clean positive decimal row")
expect(suffix).to_contain("ios_render_log_validation_status=fail")
expect(suffix).to_contain("ios_render_log_validation_reason=ios-render-log-html-len-malformed")
expect(suffix).to_contain("ios_render_log_marker_status=fail")
expect(suffix).to_contain("ios_render_log_html_len=")
expect(zero).to_contain("ios_render_log_validation_status=fail")
expect(zero).to_contain("ios_render_log_validation_reason=ios-render-log-html-len-malformed")
expect(zero).to_contain("ios_render_log_marker_status=fail")
expect(zero).to_contain("ios_render_log_html_len=")
expect(huge).to_contain("ios_render_log_validation_status=fail")
expect(huge).to_contain("ios_render_log_validation_reason=ios-render-log-html-len-malformed")
expect(huge).to_contain("ios_render_log_marker_status=fail")
expect(huge).to_contain("ios_render_log_html_len=")
expect(huge.contains("ios_render_log_html_len=10000001")).to_equal(false)
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
expect(evidence).to_contain("ios_render_log_validation_reason=ios-metal-log-marker-missing")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=fail")
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

#### rejects generic Metal readiness text even with CAMetalLayer context

- Confirm iOS Metal readiness is tied to CAMetalLayer or native Metal runtime evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-generic-metal-ready"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nMetal renderer ready\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm iOS Metal readiness is tied to CAMetalLayer or native Metal runtime evidence")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-metal-log-marker-missing")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=fail")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
```

</details>

#### rejects fallback GPU markers in iOS Metal render logs

- Confirm fallback GPU text cannot coexist with iOS Metal proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-fallback-gpu"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\nGPU fallback renderer: SwiftShader software renderer\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm fallback GPU text cannot coexist with iOS Metal proof")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-render-log-fallback-gpu")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_marker_status=pass")
expect(evidence).to_contain("ios_render_log_fallback_marker_status=fail")
expect(evidence).to_contain("ios_render_log_tauri_context_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
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

Runnable source: 18 lines folded for reproduction.
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
expect(evidence).to_contain("ios_render_log_symlink_source_count=0")
expect(evidence).to_contain("ios_render_log_hardlink_source_count=0")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
```

</details>

#### rejects empty requested iOS log source paths

- Confirm valid iOS render evidence cannot hide an empty requested source


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
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
expect(evidence).to_contain("ios_render_log_symlink_source_count=0")
expect(evidence).to_contain("ios_render_log_hardlink_source_count=0")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
```

</details>

#### rejects symlinked requested iOS log source paths

- Confirm iOS render logs cannot be substituted through symlinked sources


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-symlink-source"
val command = "rm -rf " + root + " " + root + "-external && mkdir -p " + root + " " + root + "-external && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "-external/ios.log && " +
    "ln -s ../test-tauri-ios-render-log-validator-symlink-source-external/ios.log " + root + "/linked.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log " + root + "/linked.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm iOS render logs cannot be substituted through symlinked sources")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-render-log-source-symlink")
expect(evidence).to_contain("ios_render_log_requested_source_count=2")
expect(evidence).to_contain("ios_render_log_source_count=1")
expect(evidence).to_contain("ios_render_log_missing_source_count=0")
expect(evidence).to_contain("ios_render_log_empty_source_count=0")
expect(evidence).to_contain("ios_render_log_symlink_source_count=1")
expect(evidence).to_contain("ios_render_log_hardlink_source_count=0")
expect(evidence).to_contain("ios_render_log_nonregular_source_count=0")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
```

</details>

#### rejects hardlinked requested iOS log source paths

- Confirm iOS render logs cannot be substituted through hardlinked sources


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-hardlink-source"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/original.log && " +
    "ln " + root + "/original.log " + root + "/linked.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log " + root + "/linked.log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm iOS render logs cannot be substituted through hardlinked sources")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-render-log-source-hardlink")
expect(evidence).to_contain("ios_render_log_requested_source_count=2")
expect(evidence).to_contain("ios_render_log_source_count=1")
expect(evidence).to_contain("ios_render_log_missing_source_count=0")
expect(evidence).to_contain("ios_render_log_empty_source_count=0")
expect(evidence).to_contain("ios_render_log_symlink_source_count=0")
expect(evidence).to_contain("ios_render_log_hardlink_source_count=1")
expect(evidence).to_contain("ios_render_log_nonregular_source_count=0")
expect(evidence).to_contain("ios_render_log_marker_status=pass")
expect(evidence).to_contain("ios_render_log_metal_context_status=pass")
```

</details>

#### rejects non regular requested iOS log source paths

- Confirm iOS render logs cannot be substituted through non-regular sources


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-ios-render-log-validator-nonregular-source"
val command = "rm -rf " + root + " && mkdir -p " + root + "/not-a-log && " +
    "printf '[tauri-shell] creating window from app://index.html\\n[tauri-shell] ios renderer context: backend=WKWebView metal_expected=true metal_layer=CAMetalLayer\\n[tauri-shell] render, html_len=347702\\nCAMetalLayer Metal renderer ready\\n' > " + root + "/ios.log && " +
    "node scripts/check/validate-tauri-ios-render-log-proof.js " + root + "/ios.log " + root + "/not-a-log > " + root + "/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/evidence.env")
step("Confirm iOS render logs cannot be substituted through non-regular sources")
expect(evidence).to_contain("ios_render_log_validation_status=fail")
expect(evidence).to_contain("ios_render_log_validation_reason=ios-render-log-source-not-regular")
expect(evidence).to_contain("ios_render_log_requested_source_count=2")
expect(evidence).to_contain("ios_render_log_source_count=1")
expect(evidence).to_contain("ios_render_log_missing_source_count=0")
expect(evidence).to_contain("ios_render_log_empty_source_count=0")
expect(evidence).to_contain("ios_render_log_symlink_source_count=0")
expect(evidence).to_contain("ios_render_log_hardlink_source_count=0")
expect(evidence).to_contain("ios_render_log_nonregular_source_count=1")
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

Runnable source: 49 lines folded for reproduction.
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
expect(evidence).to_contain("ios_render_log_symlink_source_count=0")
expect(evidence).to_contain("ios_render_log_hardlink_source_count=0")
expect(evidence).to_contain("ios_render_log_nonregular_source_count=0")
expect(evidence).to_contain("ios_render_log_source_coherence_status=")
expect(evidence).to_contain("ios_render_log_coherent_source_path=")
expect(evidence).to_contain("ios_render_log_coherent_source_size_bytes=")
expect(evidence).to_contain("ios_render_log_marker_status=")
expect(evidence).to_contain("ios_render_log_html_len=")
expect(evidence).to_contain("ios_render_log_metal_marker_status=")
expect(evidence).to_contain("ios_render_log_fallback_marker_status=")
expect(evidence).to_contain("ios_render_log_tauri_context_status=")
expect(evidence).to_contain("ios_render_log_metal_context_status=")
expect(evidence).to_contain("ios_render_log_failure_marker_status=")
expect(evidence).to_contain("ios_mdi_proof_status=")
expect(evidence).to_contain("ios_mdi_failure_marker_status=")
expect(evidence).to_contain("ios_mdi_proof_requested_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_marker_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_missing_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_symlink_source_count=0")
expect(evidence).to_contain("ios_mdi_proof_empty_source_count=0")
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

#### preserves validator-derived rows when wrapper diagnostics fail

- Confirm fail diagnostics reuse existing validator env rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = file_read("scripts/check/check-tauri-ios-mobile-renderer-evidence.shs")
step("Confirm fail diagnostics reuse existing validator env rows")
expect(direct).to_contain("emit_existing_or_default")
expect(direct).to_contain("emit_existing_or_default ios_render_log_validation_status \"$diagnostic_status\" \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_validation_reason \"$diagnostic_reason\" \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_source_coherence_status \"$diagnostic_status\" \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_coherent_source_path \"\" \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_coherent_source_size_bytes \"\" \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_symlink_source_count 0 \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_hardlink_source_count 0 \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_nonregular_source_count 0 \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_tauri_context_status \"$diagnostic_status\" \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_metal_context_status \"$diagnostic_status\" \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_render_log_fallback_marker_status \"$diagnostic_status\" \"$IOS_RENDER_LOG_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_mdi_proof_status \"$diagnostic_status\" \"$MDI_PROOF_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_mdi_failure_marker_status \"$diagnostic_status\" \"$MDI_PROOF_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_mdi_proof_symlink_source_count 0 \"$MDI_PROOF_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_mdi_event_status \"$diagnostic_status\" \"$MDI_PROOF_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_mdi_interaction_latency_status \"$diagnostic_status\" \"$MDI_PROOF_VALIDATION_ENV\"")
expect(direct).to_contain("emit_existing_or_default ios_mdi_animation_status \"$diagnostic_status\" \"$MDI_PROOF_VALIDATION_ENV\"")
```

</details>

#### keeps the iOS renderer wrappers and Tauri shell wired to the validator

<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = file_read("scripts/check/check-tauri-ios-mobile-renderer-evidence.shs")
val aggregate = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
val tauri = file_read("tools/tauri-shell/src-tauri/src/lib.rs")
val validator = file_read("scripts/check/validate-tauri-ios-render-log-proof.js")
expect(validator).to_contain("const maxRenderHtmlLen = 10000000")
expect(validator).to_contain("coherentSourceHtmlLen")
expect(validator).to_contain("CAMetalLayer\\\\s+Metal renderer ready")
expect(direct).to_contain("validate-tauri-ios-render-log-proof.js")
expect(direct).to_contain("ios_render_log.validation.env")
expect(direct).to_contain("ios_mdi_proof.validation.env")
expect(direct).to_contain("emit_unavailable_ios_diagnostics")
expect(direct).to_contain("value_of ios_render_log_validation_status")
expect(direct).to_contain("ios_render_log_empty_source_count=$ios_render_log_empty_source_count")
expect(direct).to_contain("ios_render_log_symlink_source_count=$ios_render_log_symlink_source_count")
expect(direct).to_contain("ios_render_log_hardlink_source_count=$ios_render_log_hardlink_source_count")
expect(direct).to_contain("ios_render_log_nonregular_source_count=$ios_render_log_nonregular_source_count")
expect(direct).to_contain("ios_render_log_source_coherence_status=$ios_render_log_source_coherence_status")
expect(direct).to_contain("ios_render_log_coherent_source_path=$ios_render_log_coherent_source_path")
expect(direct).to_contain("ios_render_log_coherent_source_size_bytes=$ios_render_log_coherent_source_size_bytes")
expect(direct).to_contain("ios_render_log_tauri_context_status=$ios_render_log_tauri_context_status")
expect(direct).to_contain("ios_render_log_metal_context_status=$ios_render_log_metal_context_status")
expect(direct).to_contain("ios_render_log_fallback_marker_status=$ios_render_log_fallback_marker_status")
expect(direct).to_contain("value_of ios_mdi_proof_status")
expect(direct).to_contain("ios_mdi_animation_frame_count")
expect(direct).to_contain("ios_mdi_input_to_paint_ms")
expect(direct).to_contain("ios_mdi_interaction_latency_status")
expect(direct).to_contain("ios_mdi_failure_marker_status")
expect(direct).to_contain("ios_mdi_proof_marker_source_count")
expect(direct).to_contain("ios_mdi_proof_symlink_source_count")
expect(direct).to_contain("ios_mdi_event_body_click_routed")
expect(direct).to_contain("ios_mdi_event_taskbar_labels_visible")
expect(aggregate).to_contain("TAURI_MOBILE_RENDERER_IOS_RENDER_LOG_VALIDATOR")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_requested_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_missing_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_empty_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_symlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_hardlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_nonregular_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_html_len")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_source_coherence_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_path")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_coherent_source_size_bytes")
expect(aggregate).to_contain("ios-render-log-coherent-source-missing")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_tauri_context_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_metal_context_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_render_log_fallback_marker_status")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_body_click_routed")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_marker_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_proof_symlink_source_count")
expect(aggregate).to_contain("tauri_mobile_renderer_parity_ios_mdi_event_taskbar_labels_visible")
expect(aggregate).to_contain("ios-tauri-wkwebview-context-missing")
expect(aggregate).to_contain("ios-metal-context-missing")
expect(aggregate).to_contain("ios-render-log-source-mismatch")
expect(aggregate).to_contain("ios-render-log-fallback-gpu")
expect(aggregate).to_contain("ios-render-log-source-missing")
expect(aggregate).to_contain("ios-render-log-source-empty")
expect(aggregate).to_contain("ios-render-log-source-symlink")
expect(aggregate).to_contain("ios-render-log-source-hardlink")
expect(aggregate).to_contain("ios-render-log-source-not-regular")
expect(tauri).to_contain("ios renderer context: backend=WKWebView")
expect(tauri).to_contain("metal_layer=CAMetalLayer")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
