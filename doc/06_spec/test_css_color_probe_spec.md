# Test Css Color Probe Specification

> <details>

<!-- sdn-diagram:id=test_css_color_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_css_color_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_css_color_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_css_color_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Css Color Probe Specification

## Scenarios

### css color probe

#### rgb comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport("<html><body style='background-color: rgb(37, 99, 235)'></body></html>", 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF2563EBu32)
```

</details>

#### rgb space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport("<html><body style='background-color: rgb(5 150 105)'></body></html>", 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### hex3 shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport("<html><body style='background-color: #0f8'></body></html>", 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### background shorthand rebeccapurple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport("<html><body style='background: rebeccapurple no-repeat'></body></html>", 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### background shorthand rgb no-repeat

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport("<html><body style='background: rgb(5, 150, 105) no-repeat'></body></html>", 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### background url then hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport("<html><body style='background: url(hero.png) #0f8 no-repeat'></body></html>", 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/test_css_color_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- css color probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
