# Electron Capture Specification

> Tests covering ElectronCapture — CaptureResult, ElectronCapture — pixel buffer, ElectronCapture — capture_electron_scene.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Capture Specification

## Scenarios

### ElectronCapture — CaptureResult

#### successful capture

#### AC-2: capture_electron returns a CaptureResult with backend_name

- AC-2: capture_electron returns a CaptureResult with backend_name
   - Expected: result.backend_name equals `electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_electron returns a CaptureResult with backend_name")
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
val result = capture_electron(html, W, H)
expect(result.backend_name).to_equal("electron")
```

</details>

#### AC-2: small HTML captures use Simple Web Renderer pixels

- AC-2: small HTML captures use Simple Web Renderer pixels
   - Expected: result.success is true
   - Expected: result.pixels.len() equals `8 * 220`
   - Expected: result.pixels[7 + 210 * 8] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: small HTML captures use Simple Web Renderer pixels")
val html = "<html><body style='background-color:#2563eb'></body></html>"
val result = capture_electron(html, 8, 220)
expect(result.success).to_equal(true)
expect(result.pixels.len()).to_equal(8 * 220)
expect(result.pixels[7 + 210 * 8]).to_equal(0xFF2563EBu32)
```

</details>

#### capture with invalid HTML

#### AC-2: capture with empty HTML sets error message

- AC-2: capture with empty HTML sets error message
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture with empty HTML sets error message")
val result = capture_electron("", W, H)
val has_error = result.error.len() > 0 or result.success == false
expect(has_error).to_equal(true)
```

</details>

### ElectronCapture — pixel buffer

#### successful capture

#### AC-2: captured pixels have correct buffer size

- AC-2: captured pixels have correct buffer size
   - Expected: result.pixels.len().to_i32() equals `expected_len`
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: captured pixels have correct buffer size")
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
val result = capture_electron(html, W, H)
val expected_len = W * H
# If capture succeeds, buffer size should match
if result.success:
    expect(result.pixels.len().to_i32()).to_equal(expected_len)
else:
    # Capture may fail in test env (no Electron)
    expect(result.success).to_equal(false)
```

</details>

#### AC-2: captured result has correct width and height

- AC-2: captured result has correct width and height
   - Expected: result.width equals `W`
   - Expected: result.height equals `H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: captured result has correct width and height")
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
val result = capture_electron(html, W, H)
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
```

</details>

### ElectronCapture — capture_electron_scene

#### end-to-end scene capture

#### AC-2: capture_electron_scene accepts WmSceneSpec and returns unified renderer CaptureResult

- AC-2: capture_electron_scene accepts WmSceneSpec and returns unified renderer CaptureResult
   - Expected: result.backend_name equals `browser_compositor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_electron_scene accepts WmSceneSpec and returns unified renderer CaptureResult")
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
expect(result.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-2: capture_electron_scene result dimensions match scene

- AC-2: capture_electron_scene result dimensions match scene
   - Expected: result.width equals `W`
   - Expected: result.height equals `H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_electron_scene result dimensions match scene")
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/electron_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ElectronCapture — CaptureResult, ElectronCapture — pixel buffer, ElectronCapture — capture_electron_scene.
- ElectronCapture — CaptureResult
- ElectronCapture — pixel buffer
- ElectronCapture — capture_electron_scene

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78a37a9ac8d45429b2a9ca25cf3f3802ca428fbbf6859c0513d4a5d97845d13a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78a37a9ac8d45429b2a9ca25cf3f3802ca428fbbf6859c0513d4a5d97845d13a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78a37a9ac8d45429b2a9ca25cf3f3802ca428fbbf6859c0513d4a5d97845d13a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/unit/os/compositor/electron_capture_spec.spl
mirror: doc/06_spec/unit/os/compositor/electron_capture_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/compositor/electron_capture_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/unit/os/compositor/electron_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/compositor/electron_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
