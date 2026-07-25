# Wm Unified Renderer Specification

> <details>

<!-- sdn-diagram:id=wm_unified_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_unified_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_unified_renderer_spec -> std
wm_unified_renderer_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_unified_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Unified Renderer Specification

## Scenarios

### WmUnifiedRenderer -- bit-identical rendering

#### host and QEMU paths

#### AC-2,AC-7: host and qemu paths produce identical pixel buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val scene = standard_wm_scene(W, H)

# Act — capture through both paths
val electron_result = capture_electron_scene(scene)
val qemu_result = capture_qemu_inprocess(scene)

# Assert — compare pixel buffers with exact match (threshold=0)
val cmp = compare_exact(
    electron_result.pixels, qemu_result.pixels, W, H)
expect(cmp.different_pixels).to_equal(0)
```

</details>

#### AC-2: repeated renders are deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val scene = standard_wm_scene(W, H)

# Act — render the same scene twice through the same path
val first = capture_qemu_inprocess(scene)
val second = capture_qemu_inprocess(scene)

# Assert — identical pixel buffers
val cmp = compare_exact(first.pixels, second.pixels, W, H)
expect(cmp.different_pixels).to_equal(0)
```

</details>

#### AC-7: different scenes produce different pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange — two scenes with different dimensions
val scene_a = standard_wm_scene(W, H)
val scene_b = standard_wm_scene(400, 300)

# Act
val result_a = render_scene_to_backend(scene_a, nil)
val result_b = render_scene_to_backend(scene_b, nil)

# Assert — pixel buffers differ (sanity check)
val same_len = result_a.len() == result_b.len()
expect(same_len).to_equal(false)
```

</details>

### WmUnifiedRenderer -- unified capture path

#### both captures use BrowserCompositorBackend

#### AC-1: capture_electron_scene uses BrowserCompositorBackend

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val scene = standard_wm_scene(W, H)

# Act
val result = capture_electron_scene(scene)

# Assert — backend_name should be "browser_compositor", not "electron_chromium"
expect(result.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-1: capture_qemu_inprocess uses BrowserCompositorBackend

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val scene = standard_wm_scene(W, H)

# Act
val result = capture_qemu_inprocess(scene)

# Assert — backend_name identifies in-process browser compositor
expect(result.backend_name).to_equal("browser_compositor")
```

</details>

### WmUnifiedRenderer -- consistency runner bit-exact mode

#### default bit-exact comparison

#### AC-5: run_consistency_check defaults to bit-exact comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val scene = standard_wm_scene(W, H)
val profile = profile_strict()

# Act
val report = run_consistency_check(scene, profile)

# Assert — 100% match and passed
expect(report.overall.match_percentage).to_equal(10000)
expect(report.passed).to_equal(true)
```

</details>

#### AC-5: bit-exact mode reports 0 differing pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val scene = standard_wm_scene(W, H)
val profile = profile_strict()

# Act
val report = run_consistency_check(scene, profile)

# Assert — zero pixel differences
expect(report.overall.different_pixels).to_equal(0)
```

</details>

### WmUnifiedRenderer -- preview display path

#### Electron display-only mode

#### AC-3: display_in_electron produces PPM file from pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange — render scene to get pixel buffer
val scene = standard_wm_scene(W, H)
val pixels = render_scene_to_backend(scene, nil)

# Act — display sends pre-rendered pixels to Electron
val result = display_in_electron(pixels, W, H)

# Assert — result indicates success and PPM file was created
expect(result.success).to_equal(true)
```

</details>

#### AC-4: scene_to_html still works for preview

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val scene = standard_wm_scene(W, H)

# Act
val html = scene_to_html(scene)

# Assert — HTML output is non-empty and contains expected markup
val has_content = html.len() > 0
expect(has_content).to_equal(true)
val has_div = html.contains("<div") or html.contains("<DIV")
expect(has_div).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_unified_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WmUnifiedRenderer -- bit-identical rendering
- WmUnifiedRenderer -- unified capture path
- WmUnifiedRenderer -- consistency runner bit-exact mode
- WmUnifiedRenderer -- preview display path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
