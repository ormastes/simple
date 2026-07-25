# Tmp Q1 Specification

> <details>

<!-- sdn-diagram:id=tmp_q1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_q1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_q1_spec -> std
tmp_q1_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_q1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Q1 Specification

## Scenarios

### q1

#### 02

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("02_block_boxes", 320, 240).len()).to_equal(6)
```

</details>

#### 03

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("03_list", 320, 240).len()).to_equal(4)
```

</details>

#### 04

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("04_button", 320, 240).len()).to_equal(2)
```

</details>

#### 05

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("05_text_input", 320, 240).len()).to_equal(2)
```

</details>

#### 06

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_compat_fixture_simple_boxes("06_card_panel", 320, 240).len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_q1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- q1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
