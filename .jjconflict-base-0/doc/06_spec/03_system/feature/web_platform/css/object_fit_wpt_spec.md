# Object Fit Wpt Specification

> <details>

<!-- sdn-diagram:id=object_fit_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=object_fit_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

object_fit_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=object_fit_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Object Fit Wpt Specification

## Scenarios

### WPT-derived CSS object-fit subset

#### compute_object_fit pure function

#### fill stretches to box dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_object_fit(100.0, 50.0, 200.0, 200.0, "fill", "50% 50%")
expect(approx(result.dest_width, 200.0)).to_equal(true)
expect(approx(result.dest_height, 200.0)).to_equal(true)
```

</details>

#### contain preserves aspect ratio within box

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_object_fit(200.0, 100.0, 100.0, 100.0, "contain", "50% 50%")
expect(approx(result.dest_width, 100.0)).to_equal(true)
expect(approx(result.dest_height, 50.0)).to_equal(true)
```

</details>

#### cover fills box preserving aspect ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_object_fit(200.0, 100.0, 100.0, 100.0, "cover", "50% 50%")
expect(approx(result.dest_width, 200.0)).to_equal(true)
expect(approx(result.dest_height, 100.0)).to_equal(true)
```

</details>

#### none uses natural dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_object_fit(50.0, 30.0, 100.0, 100.0, "none", "50% 50%")
expect(approx(result.dest_width, 50.0)).to_equal(true)
expect(approx(result.dest_height, 30.0)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/object_fit_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived CSS object-fit subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
