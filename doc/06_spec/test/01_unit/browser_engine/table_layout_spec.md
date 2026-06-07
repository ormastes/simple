# Table Layout Specification

> <details>

<!-- sdn-diagram:id=table_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=table_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

table_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=table_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Table Layout Specification

## Scenarios

### table layout basic table

#### AC-5: single-row single-cell table produces one row

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _table_layout("<table><tr><td>cell</td></tr></table>")
val rows = _row_count(box_)
expect(rows).to_equal(1)
```

</details>

#### AC-5: two-row table produces two rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _table_layout("<table><tr><td>r1</td></tr><tr><td>r2</td></tr></table>")
val rows = _row_count(box_)
expect(rows).to_equal(2)
```

</details>

#### AC-5: table has positive height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _table_layout("<table><tr><td>cell</td></tr></table>")
expect(box_.height).to_be_greater_than(0)
```

</details>

#### AC-5: table width does not exceed container width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _table_layout("<table><tr><td>cell</td></tr></table>")
expect(box_.width).to_be_less_than(601)
```

</details>

### table layout colspan

#### AC-5: cell with colspan=2 is wider than adjacent normal cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _table_layout(
    "<table><tr><td colspan=\"2\">wide</td><td>narrow</td></tr><tr><td>a</td><td>b</td><td>c</td></tr></table>")
val first_row = box_.children[0]
if first_row.children.len() > 0:
    val wide = first_row.children[0]
    val narrow = first_row.children[1]
    expect(wide.width).to_be_greater_than(narrow.width)
else:
    expect(first_row.children.len()).to_be_greater_than(0)
```

</details>

### table layout auto column widths

#### AC-5: column widths sum equals table width for equal columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _table_layout(
    "<table><tr><td>a</td><td>b</td><td>c</td></tr></table>")
val sum = _col_widths_sum(box_)
expect(sum).to_equal(box_.width)
```

</details>

#### AC-5: three equal columns have equal widths (auto layout)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _table_layout(
    "<table><tr><td>a</td><td>b</td><td>c</td></tr></table>")
val first_row = box_.children[0]
if first_row.children.len() >= 2:
    val w0 = first_row.children[0].width
    val w1 = first_row.children[1].width
    expect(w0).to_equal(w1)
else:
    expect(first_row.children.len()).to_be_greater_than(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/table_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- table layout basic table
- table layout colspan
- table layout auto column widths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
