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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates one frame per column
   - Expected: page_frame_count(page) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates one frame per column")
val page = _two_col_page()
expect(page_frame_count(page)).to_equal(2)
```

</details>

#### places columns left-to-right at different x positions

- places columns left-to-right at different x positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("places columns left-to-right at different x positions")
val page = _two_col_page()
val html = page_render_html(page)
expect(html).to_contain("left:0px")
expect(html).to_contain("left:60px")
```

</details>

#### gives every column the same width

- gives every column the same width


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("gives every column the same width")
val page = _two_col_page()
val html = page_render_html(page)
expect(html).to_contain("width:60px")
```

</details>

### publisher columns: text flow

#### fills column 0 up to its char budget with whole words

- fills column 0 up to its char budget with whole words
   - Expected: column_text(flowed, 0) equals `aaaaa bbbbb ccccc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fills column 0 up to its char budget with whole words")
val page = _two_col_page()
val flowed = flow_into_columns(page, "aaaaa bbbbb ccccc ddddd eeeee")
expect(column_text(flowed, 0)).to_equal("aaaaa bbbbb ccccc")
```

</details>

#### overflows the remaining words into column 1

- overflows the remaining words into column 1
   - Expected: column_text(flowed, 1) equals `ddddd eeeee`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("overflows the remaining words into column 1")
val page = _two_col_page()
val flowed = flow_into_columns(page, "aaaaa bbbbb ccccc ddddd eeeee")
expect(column_text(flowed, 1)).to_equal("ddddd eeeee")
```

</details>

### publisher columns: html rendering

#### includes both column divs

- includes both column divs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("includes both column divs")
val page = _two_col_page()
val flowed = flow_into_columns(page, "aaaaa bbbbb ccccc ddddd eeeee")
val html = columns_render_html(flowed)
expect(html).to_contain("id=\"col0\"")
expect(html).to_contain("id=\"col1\"")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks the hand-computed word split ground truth

- sanity-checks the hand-computed word split ground truth
   - Expected: column_text(flowed, 1) equals `ddddd eeeee`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sanity-checks the hand-computed word split ground truth")
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
| Updated | 2026-08-26 |
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b302c4ebb58af40ef328e741ae1da70f8dc85fd589a1b73461244370444c1629`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b302c4ebb58af40ef328e741ae1da70f8dc85fd589a1b73461244370444c1629`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b302c4ebb58af40ef328e741ae1da70f8dc85fd589a1b73461244370444c1629`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/office/publisher/columns_spec.spl
mirror: doc/06_spec/01_unit/app/office/publisher/columns_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/publisher/columns_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/publisher/columns_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/publisher/columns_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/publisher/columns_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates one frame per column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/publisher/columns_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places columns left-to-right at different x positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/publisher/columns_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives every column the same width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
