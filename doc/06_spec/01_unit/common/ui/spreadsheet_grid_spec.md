# Spreadsheet Grid Specification

> Tests covering shared spreadsheet grid layout.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spreadsheet Grid Specification

## Scenarios

### shared spreadsheet grid layout

#### defines Calc's twenty-column viewport through the common UI grid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines Calc's twenty-column viewport through the common UI grid
   - Expected: metrics.visible_columns equals `20`
   - Expected: metrics.visible_rows equals `30`
   - Expected: spreadsheet_grid_width(metrics) equals `124`
   - Expected: spreadsheet_grid_column_label(0) equals `A`
   - Expected: spreadsheet_grid_column_label(19) equals `T`
   - Expected: spreadsheet_grid_column_label(26) equals `AA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("defines Calc's twenty-column viewport through the common UI grid")
val metrics = spreadsheet_grid_default_metrics()
expect(metrics.visible_columns).to_equal(20)
expect(metrics.visible_rows).to_equal(30)
expect(spreadsheet_grid_width(metrics)).to_equal(124)
expect(spreadsheet_grid_column_label(0)).to_equal("A")
expect(spreadsheet_grid_column_label(19)).to_equal("T")
expect(spreadsheet_grid_column_label(26)).to_equal("AA")
```

</details>

#### uses common layout grid placement for stable cell identifiers

- uses common layout grid placement for stable cell identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("uses common layout grid placement for stable cell identifiers")
val metrics = spreadsheet_grid_metrics(2, 2, 6, 4)
val grid = spreadsheet_grid_widget("grid", [
    button("cell_A1", "", "select"),
    button("cell_B1", "", "select"),
    button("cell_A2", "", "select")
], metrics)
val rects = compute_layout(grid, 0, 0, 12, 2)
match find_rect(rects, "cell_A1"):
    case Some(a1):
        match find_rect(rects, "cell_B1"):
            case Some(b1):
                expect(b1.x).to_be_greater_than(a1.x)
            case _:
                fail("common layout omitted cell_B1")
        match find_rect(rects, "cell_A2"):
            case Some(a2):
                expect(a2.y).to_be_greater_than(a1.y)
            case _:
                fail("common layout omitted cell_A2")
    case _:
        fail("common layout omitted cell_A1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/ui/spreadsheet_grid_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering shared spreadsheet grid layout.
- shared spreadsheet grid layout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMMON`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b495afb66be118bbe83e84d910a57907153e598ea6577912ec7aa274f477624`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b495afb66be118bbe83e84d910a57907153e598ea6577912ec7aa274f477624`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b495afb66be118bbe83e84d910a57907153e598ea6577912ec7aa274f477624`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/common/ui/spreadsheet_grid_spec.spl
mirror: doc/06_spec/01_unit/common/ui/spreadsheet_grid_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/ui/spreadsheet_grid_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/ui/spreadsheet_grid_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/ui/spreadsheet_grid_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/common/ui/spreadsheet_grid_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines Calc's twenty-column viewport through the common UI grid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/ui/spreadsheet_grid_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses common layout grid placement for stable cell identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
