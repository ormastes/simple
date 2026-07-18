# Test Fixture Probe Specification

> <details>

<!-- sdn-diagram:id=test_fixture_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_fixture_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_fixture_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_fixture_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Fixture Probe Specification

## Scenarios

### fixture probe

#### CSS background fixture pixel[0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[0]).to_equal(0xFFF0F0F8u32)
```

</details>

#### CSS color fixture pixel at 8,8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("10_colors"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[8 + 8 * 40]).to_equal(0xFFDBEAFEu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/test_fixture_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- fixture probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
