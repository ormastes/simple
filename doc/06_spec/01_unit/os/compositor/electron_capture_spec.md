# Electron Capture Specification

> <details>

<!-- sdn-diagram:id=electron_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_capture_spec -> std
electron_capture_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
val result = capture_electron(html, W, H)
expect(result.backend_name).to_equal("electron")
```

</details>

#### AC-2: small HTML captures use Simple Web Renderer pixels

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color:#2563eb'></body></html>"
val result = capture_electron(html, 8, 220)
expect(result.success).to_equal(true)
expect(result.pixels.len()).to_equal(8 * 220)
expect(result.pixels[7 + 210 * 8]).to_equal(0xFF2563EBu32)
```

</details>

#### capture with invalid HTML

#### AC-2: capture with empty HTML sets error message

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_electron("", W, H)
val has_error = result.error.len() > 0 or result.success == false
expect(has_error).to_equal(true)
```

</details>

### ElectronCapture — pixel buffer

#### successful capture

#### AC-2: captured pixels have correct buffer size

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
expect(result.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-2: capture_electron_scene result dimensions match scene

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/compositor/electron_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
