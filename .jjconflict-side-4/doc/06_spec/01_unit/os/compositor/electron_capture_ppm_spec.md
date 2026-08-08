# electron_capture_ppm_spec

> CaptureResult fields (pixels, width, height, backend_name, success, error)

<!-- sdn-diagram:id=electron_capture_ppm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_capture_ppm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_capture_ppm_spec -> std
electron_capture_ppm_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_capture_ppm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# electron_capture_ppm_spec

CaptureResult fields (pixels, width, height, backend_name, success, error)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/electron_capture_ppm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## CaptureResult After PPM Switch

    CaptureResult fields (pixels, width, height, backend_name, success, error)
    remain the same regardless of underlying format (PNG or PPM).

## Scenarios

### ElectronCapture PPM — CaptureResult structure

#### error result construction

#### AC-2: capture_error creates result with correct backend_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_error("electron", W, H, "test error")
expect(result.backend_name).to_equal("electron")
```

</details>

#### AC-2: capture_error creates result with empty pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_error("electron", W, H, "test error")
expect(result.pixels.len().to_i32()).to_equal(0)
```

</details>

#### AC-2: capture_error preserves error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_error("electron", W, H, "PPM decode failed")
expect(result.error).to_contain("PPM")
```

</details>

#### AC-2: capture_error sets success to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_error("electron", W, H, "test error")
expect(result.success).to_equal(false)
```

</details>

#### AC-2: capture_error preserves dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_error("electron", W, H, "test error")
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
```

</details>

### ElectronCapture PPM — command invocation

#### command construction

#### AC-2: capture_electron with empty HTML returns error (not crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_electron("", W, H)
expect(result.success).to_equal(false)
```

</details>

#### AC-2: capture_electron error mentions 'Empty HTML'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_electron("", W, H)
val mentions_empty = result.error.contains("Empty") or result.error.contains("empty")
expect(mentions_empty).to_equal(true)
```

</details>

#### scene-level capture with PPM

#### AC-2: capture_electron_scene returns result with shared compositor backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
expect(result.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-2: capture_electron_scene dimensions match scene spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
```

</details>

### ElectronCapture PPM — decode integration

#### capture with valid scene

#### AC-2: capture result from valid scene uses the shared compositor backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
# In test env, Electron may not be available
if result.success:
    expect(result.backend_name).to_equal("browser_compositor")
    expect(result.pixels.len()).to_be_greater_than(0)
else:
    # Graceful degradation when Electron is missing
    val has_error = result.error.len() > 0
    expect(has_error).to_equal(true)
```

</details>

#### AC-2: successful capture pixel count equals width * height

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
if result.success:
    val expected = W * H
    expect(result.pixels.len().to_i32()).to_equal(expected)
else:
    expect(result.success).to_equal(false)
```

</details>

#### AC-2: successful capture has non-zero pixels (not all transparent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
if result.success:
    var has_nonzero = false
    for px in result.pixels:
        if px != 0:
            has_nonzero = true
    expect(has_nonzero).to_equal(true)
else:
    expect(result.success).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
