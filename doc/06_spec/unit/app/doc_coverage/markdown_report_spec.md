# Markdown Report Specification

> Tests covering generate_coverage_markdown structure, generate_coverage_markdown summary, generate_coverage_markdown scope breakdown, generate_coverage_markdown top files, generate_coverage_markdown missing sdoctests, generate_coverage_markdown syntax, generate_coverage_markdown status indicators, generate_coverage_markdown empty cases, generate_coverage_markdown integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown Report Specification

## Scenarios

### generate_coverage_markdown structure

#### includes title header

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- includes title header
   - Expected: has_title is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes title header")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_title = md.contains("# Documentation Coverage Report")
expect(has_title).to_equal(true)
```

</details>

#### includes summary section

- includes summary section
   - Expected: has_summary is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes summary section")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_summary = md.contains("## Summary")
expect(has_summary).to_equal(true)
```

</details>

#### includes coverage by scope section

- includes coverage by scope section
   - Expected: has_scope is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes coverage by scope section")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_scope = md.contains("## Coverage by Scope")
expect(has_scope).to_equal(true)
```

</details>

#### includes top files section

- includes top files section
   - Expected: has_top_files is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes top files section")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_top_files = md.contains("## Top 10 Files Needing Documentation")
expect(has_top_files).to_equal(true)
```

</details>

#### includes missing sdoctests section

- includes missing sdoctests section
   - Expected: has_missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes missing sdoctests section")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_missing = md.contains("## Missing SDoctest Examples")
expect(has_missing).to_equal(true)
```

</details>

### generate_coverage_markdown summary

#### includes total items count

- includes total items count
   - Expected: has_total is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes total items count")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_total = md.contains("**Total Items:** 100")
expect(has_total).to_equal(true)
```

</details>

#### includes documented count

- includes documented count
   - Expected: has_documented is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes documented count")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_documented = md.contains("**Documented:** 75")
expect(has_documented).to_equal(true)
```

</details>

#### includes missing docs count

- includes missing docs count
   - Expected: has_missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes missing docs count")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_missing = md.contains("**Missing Docs:** 25")
expect(has_missing).to_equal(true)
```

</details>

#### includes overall status indicator

- includes overall status indicator
   - Expected: has_status is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes overall status indicator")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_status = md.contains("**Overall Status:**")
expect(has_status).to_equal(true)
```

</details>

#### includes sdoctest coverage

- includes sdoctest coverage
   - Expected: has_sdoctest is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes sdoctest coverage")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_sdoctest = md.contains("**SDoctest Coverage:**")
expect(has_sdoctest).to_equal(true)
```

</details>

### generate_coverage_markdown scope breakdown

#### includes scope table

- includes scope table
   - Expected: has_table is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes scope table")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_table = md.contains("| Scope | Files | Items | Documented | Coverage % |")
expect(has_table).to_equal(true)
```

</details>

#### includes table separator

- includes table separator
   - Expected: has_separator is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes table separator")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_separator = md.contains("|-------|-------|-------|------------|-----------|")
expect(has_separator).to_equal(true)
```

</details>

#### groups files by scope

- groups files by scope
   - Expected: has_std is true
   - Expected: has_core is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("groups files by scope")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_std = md.contains("src/std")
val has_core = md.contains("src/core")

expect(has_std).to_equal(true)
expect(has_core).to_equal(true)
```

</details>

### generate_coverage_markdown top files

#### includes files table

- includes files table
   - Expected: has_table is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes files table")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_table = md.contains("| File | Missing Docs | Total Items | Coverage % |")
expect(has_table).to_equal(true)
```

</details>

#### lists files with missing docs

- lists files with missing docs
   - Expected: has_parser is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists files with missing docs")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_parser = md.contains("parser.spl")
expect(has_parser).to_equal(true)
```

</details>

#### shows file paths in code blocks

- shows file paths in code blocks
   - Expected: has_code_block is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows file paths in code blocks")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_code_block = md.contains("`")
expect(has_code_block).to_equal(true)
```

</details>

### generate_coverage_markdown missing sdoctests

#### includes functions table

- includes functions table
   - Expected: has_table is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes functions table")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_table = md.contains("| Function | File | Line |")
expect(has_table).to_equal(true)
```

</details>

#### lists functions without sdoctests

- lists functions without sdoctests
   - Expected: has_trim is true
   - Expected: has_parse is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists functions without sdoctests")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_trim = md.contains("trim")
val has_parse = md.contains("parse")

expect(has_trim).to_equal(true)
expect(has_parse).to_equal(true)
```

</details>

#### shows line numbers

- shows line numbers
   - Expected: has_line_10 is true
   - Expected: has_line_20 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows line numbers")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_line_10 = md.contains("| 10 |") or md.contains(" 10 |")
val has_line_20 = md.contains("| 20 |") or md.contains(" 20 |")

expect(has_line_10).to_equal(true)
expect(has_line_20).to_equal(true)
```

</details>

### generate_coverage_markdown syntax

#### uses proper header syntax

- uses proper header syntax
   - Expected: has_h1 is true
   - Expected: has_h2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses proper header syntax")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_h1 = md.contains("# ")
val has_h2 = md.contains("## ")

expect(has_h1).to_equal(true)
expect(has_h2).to_equal(true)
```

</details>

#### uses proper table syntax

- uses proper table syntax
   - Expected: has_pipes is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses proper table syntax")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_pipes = md.contains("|")
expect(has_pipes).to_equal(true)
```

</details>

#### uses proper bold syntax

- uses proper bold syntax
   - Expected: has_bold is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses proper bold syntax")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_bold = md.contains("**")
expect(has_bold).to_equal(true)
```

</details>

#### uses proper code block syntax

- uses proper code block syntax
   - Expected: has_backticks is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses proper code block syntax")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_backticks = md.contains("`")
expect(has_backticks).to_equal(true)
```

</details>

### generate_coverage_markdown status indicators

#### shows status emoji for overall coverage

- shows status emoji for overall coverage
   - Expected: has_emoji is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows status emoji for overall coverage")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_emoji = md.contains("✅") or md.contains("⚠️") or md.contains("❌")
expect(has_emoji).to_equal(true)
```

</details>

### generate_coverage_markdown empty cases

#### handles report with no files

- handles report with no files
   - Expected: has_summary is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles report with no files")
var report = CoverageReport.create()
report.total_items = 0
report.documented_items = 0
report.missing_docs = 0

val md = generate_coverage_markdown(report)

val has_summary = md.contains("## Summary")
expect(has_summary).to_equal(true)
```

</details>

#### handles files with no items

- handles files with no items
   - Expected: has_structure is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles files with no items")
var report = CoverageReport.create()
var file = FileCoverage.create("src/empty.spl")
file.total_items = 0
report.files = [file]

val md = generate_coverage_markdown(report)

val has_structure = md.contains("# Documentation Coverage Report")
expect(has_structure).to_equal(true)
```

</details>

### generate_coverage_markdown integration

#### generates complete report with all sections

- generates complete report with all sections
   - Expected: has_title is true
   - Expected: has_summary is true
   - Expected: has_scope is true
   - Expected: has_top is true
   - Expected: has_missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates complete report with all sections")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_title = md.contains("# Documentation Coverage Report")
val has_summary = md.contains("## Summary")
val has_scope = md.contains("## Coverage by Scope")
val has_top = md.contains("## Top 10 Files")
val has_missing = md.contains("## Missing SDoctest")

expect(has_title).to_equal(true)
expect(has_summary).to_equal(true)
expect(has_scope).to_equal(true)
expect(has_top).to_equal(true)
expect(has_missing).to_equal(true)
```

</details>

#### formats numbers correctly

- formats numbers correctly
   - Expected: has_numbers is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats numbers correctly")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_numbers = md.contains("100") and md.contains("75") and md.contains("25")
expect(has_numbers).to_equal(true)
```

</details>

#### produces valid markdown that could be rendered

- produces valid markdown that could be rendered
   - Expected: has_newlines is true
   - Expected: has_headers is true
   - Expected: has_tables is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces valid markdown that could be rendered")
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_newlines = md.contains("\n")
val has_headers = md.contains("#")
val has_tables = md.contains("|")

expect(has_newlines).to_equal(true)
expect(has_headers).to_equal(true)
expect(has_tables).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/doc_coverage/markdown_report_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering generate_coverage_markdown structure, generate_coverage_markdown summary, generate_coverage_markdown scope breakdown, generate_coverage_markdown top files, generate_coverage_markdown missing sdoctests, generate_coverage_markdown syntax, generate_coverage_markdown status indicators, generate_coverage_markdown empty cases, generate_coverage_markdown integration.
- generate_coverage_markdown structure
- generate_coverage_markdown summary
- generate_coverage_markdown scope breakdown
- generate_coverage_markdown top files
- generate_coverage_markdown missing sdoctests
- generate_coverage_markdown syntax
- generate_coverage_markdown status indicators
- generate_coverage_markdown empty cases
- generate_coverage_markdown integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e7abbfa597c00098b4aec23f49c9cbda443d534a8a7cca16f57b28c6e9096e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e7abbfa597c00098b4aec23f49c9cbda443d534a8a7cca16f57b28c6e9096e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e7abbfa597c00098b4aec23f49c9cbda443d534a8a7cca16f57b28c6e9096e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/doc_coverage/markdown_report_spec.spl
mirror: doc/06_spec/unit/app/doc_coverage/markdown_report_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/doc_coverage/markdown_report_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/doc_coverage/markdown_report_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/doc_coverage/markdown_report_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes title header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/markdown_report_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes summary section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/markdown_report_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes coverage by scope section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
