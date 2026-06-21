# Emulated Capture Specification

> <details>

<!-- sdn-diagram:id=emulated_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=emulated_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

emulated_capture_spec -> std
emulated_capture_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=emulated_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Emulated Capture Specification

## Scenarios

### wm_compare emulated screenshot capture

#### Simple Web Renderer capture

#### returns a screenshot-shaped pixel buffer for a corpus sample

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val result = capture_simple_web_emulated(sample.html, 40, 30)
expect(result.success).to_equal(true)
expect(result.width).to_equal(40)
expect(result.height).to_equal(30)
expect(result.pixels.len()).to_equal(40 * 30)
```

</details>

#### rejects invalid viewport dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val result = capture_simple_web_emulated(sample.html, 0, 30)
expect(result.success).to_equal(false)
expect(result.error).to_contain("invalid viewport dimensions")
```

</details>

#### Engine2D software capture

#### returns the deterministic software backend result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[44]
val result = capture_engine2d_software_emulated(sample.html, 40, 30)
expect(result.success).to_equal(true)
expect(result.backend_name).to_equal("engine2d_software_emulated")
expect(result.pixels.len()).to_equal(40 * 30)
```

</details>

#### bitwise comparison

#### compares Simple and Engine2D emulated screenshots exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[99]
val cmp = compare_emulated_screenshots_exact(sample.html, 40, 30)
expect(cmp.different_pixels).to_equal(0)
expect(cmp.match_percentage).to_equal(10000)
```

</details>

#### does not report capture failures as exact matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[99]
val cmp = compare_emulated_screenshots_exact(sample.html, 0, 30)
expect(cmp.different_pixels).to_be_greater_than(0)
expect(cmp.match_percentage).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/emulated_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare emulated screenshot capture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
