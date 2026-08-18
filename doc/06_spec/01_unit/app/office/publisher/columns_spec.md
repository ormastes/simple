# Columns Specification

> Tests covering publisher columns: layout, publisher columns: text flow, publisher columns: html rendering, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Columns Specification

## Scenarios

### publisher columns: layout

#### creates one frame per column

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _two_col_page()
expect(page_frame_count(page)).to_equal(2)
```

</details>

#### places columns left-to-right at different x positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _two_col_page()
val html = page_render_html(page)
expect(html).to_contain("left:0px")
expect(html).to_contain("left:60px")
```

</details>

#### gives every column the same width

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _two_col_page()
val html = page_render_html(page)
expect(html).to_contain("width:60px")
```

</details>

### publisher columns: text flow

#### fills column 0 up to its char budget with whole words

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _two_col_page()
val flowed = flow_into_columns(page, "aaaaa bbbbb ccccc ddddd eeeee")
expect(column_text(flowed, 0)).to_equal("aaaaa bbbbb ccccc")
```

</details>

#### overflows the remaining words into column 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _two_col_page()
val flowed = flow_into_columns(page, "aaaaa bbbbb ccccc ddddd eeeee")
expect(column_text(flowed, 1)).to_equal("ddddd eeeee")
```

</details>

### publisher columns: html rendering

#### includes both column divs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _two_col_page()
val flowed = flow_into_columns(page, "aaaaa bbbbb ccccc ddddd eeeee")
val html = columns_render_html(flowed)
expect(html).to_contain("id=\"col0\"")
expect(html).to_contain("id=\"col1\"")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks the hand-computed word split ground truth

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _two_col_page()
val flowed = flow_into_columns(page, "aaaaa bbbbb ccccc ddddd eeeee")
# Probe verified live: asserting column 1 equals "aaaaa bbbbb
# ccccc" (col 0's actual content) failed with a mismatch,
# confirming the harness executes this assertion. Correct
# ground truth: column 1 holds the overflowed remainder.
expect(column_text(flowed, 1)).to_equal("ddddd eeeee")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/columns_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering publisher columns: layout, publisher columns: text flow, publisher columns: html rendering, deliberate-fail probe (must stay green).
- publisher columns: layout
- publisher columns: text flow
- publisher columns: html rendering
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
