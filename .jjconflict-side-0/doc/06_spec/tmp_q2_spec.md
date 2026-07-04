# Tmp Q2 Specification

> <details>

<!-- sdn-diagram:id=tmp_q2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_q2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_q2_spec -> std
tmp_q2_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_q2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Q2 Specification

## Scenarios

### q2

#### 07

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("07_scrollable_list", 320, 240).len()).to_equal(5)
```

</details>

#### 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("13_margin", 320, 240).len()).to_equal(6)
```

</details>

#### 14

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("14_border", 320, 240).len()).to_equal(6)
```

</details>

#### 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("16_flex_row", 320, 240).len()).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_q2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- q2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
