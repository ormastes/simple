# Tmp Half2 Specification

> <details>

<!-- sdn-diagram:id=tmp_half2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_half2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_half2_spec -> std
tmp_half2_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_half2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Half2 Specification

## Scenarios

### half2

#### 17

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("17_flex_col", 320, 240).len()).to_equal(6)
```

</details>

#### 18

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("18_flex_grow_weights", 320, 240).len()).to_equal(4)
```

</details>

#### 19

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("19_flex_shrink_weights", 320, 240).len()).to_equal(4)
```

</details>

#### 20

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("20_flex_basis_override", 320, 240).len()).to_equal(4)
```

</details>

#### 21

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("21_flex_wrap_basic", 320, 240).len()).to_equal(4)
```

</details>

#### 22

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("22_flex_align_items_baseline", 320, 240).len()).to_equal(3)
```

</details>

#### 23

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("23_flex_wrap_align_content_center", 320, 240).len()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_half2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- half2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
