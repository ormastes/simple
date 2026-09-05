# Table Layout Specification

> Tests covering table layout basic table, table layout colspan, table layout auto column widths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Table Layout Specification

## Scenarios

### table layout basic table

#### AC-5: single-row single-cell table produces one row

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-5: single-row single-cell table produces one row
   - Expected: rows equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: single-row single-cell table produces one row")
val box_ = _table_layout("<table><tr><td>cell</td></tr></table>")
val rows = _row_count(box_)
expect(rows).to_equal(1)
```

</details>

#### AC-5: two-row table produces two rows

- AC-5: two-row table produces two rows
   - Expected: rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: two-row table produces two rows")
val box_ = _table_layout("<table><tr><td>r1</td></tr><tr><td>r2</td></tr></table>")
val rows = _row_count(box_)
expect(rows).to_equal(2)
```

</details>

#### AC-5: table has positive height

- AC-5: table has positive height


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: table has positive height")
val box_ = _table_layout("<table><tr><td>cell</td></tr></table>")
expect(box_.height).to_be_greater_than(0)
```

</details>

#### AC-5: table width does not exceed container width

- AC-5: table width does not exceed container width


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: table width does not exceed container width")
val box_ = _table_layout("<table><tr><td>cell</td></tr></table>")
expect(box_.width).to_be_less_than(601)
```

</details>

### table layout colspan

#### AC-5: cell with colspan=2 is wider than adjacent normal cell

- AC-5: cell with colspan=2 is wider than adjacent normal cell


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: cell with colspan=2 is wider than adjacent normal cell")
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

- AC-5: column widths sum equals table width for equal columns
   - Expected: sum equals `box_.width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: column widths sum equals table width for equal columns")
val box_ = _table_layout(
    "<table><tr><td>a</td><td>b</td><td>c</td></tr></table>")
val sum = _col_widths_sum(box_)
expect(sum).to_equal(box_.width)
```

</details>

#### AC-5: three equal columns have equal widths (auto layout)

- AC-5: three equal columns have equal widths (auto layout)
   - Expected: w0 equals `w1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-5: three equal columns have equal widths (auto layout)")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering table layout basic table, table layout colspan, table layout auto column widths.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4615f729c18b24e482025a88873703ff2b298577ae82f5ea0d827ae9fc00c0a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4615f729c18b24e482025a88873703ff2b298577ae82f5ea0d827ae9fc00c0a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4615f729c18b24e482025a88873703ff2b298577ae82f5ea0d827ae9fc00c0a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/browser_engine/table_layout_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/table_layout_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/table_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/table_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/table_layout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/table_layout_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: single-row single-cell table produces one row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/table_layout_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: two-row table produces two rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/table_layout_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: table has positive height' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
