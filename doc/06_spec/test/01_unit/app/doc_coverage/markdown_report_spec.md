# Markdown Report Specification

> <details>

<!-- sdn-diagram:id=markdown_report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=markdown_report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

markdown_report_spec -> std
markdown_report_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=markdown_report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown Report Specification

## Scenarios

### generate_coverage_markdown structure

#### includes title header

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_title = md.contains("# Documentation Coverage Report")
expect(has_title).to_equal(true)
```

</details>

#### includes summary section

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_summary = md.contains("## Summary")
expect(has_summary).to_equal(true)
```

</details>

#### includes coverage by scope section

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_scope = md.contains("## Coverage by Scope")
expect(has_scope).to_equal(true)
```

</details>

#### includes top files section

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_top_files = md.contains("## Top 10 Files Needing Documentation")
expect(has_top_files).to_equal(true)
```

</details>

#### includes missing sdoctests section

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_missing = md.contains("## Missing SDoctest Examples")
expect(has_missing).to_equal(true)
```

</details>

### generate_coverage_markdown summary

#### includes total items count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_total = md.contains("**Total Items:** 100")
expect(has_total).to_equal(true)
```

</details>

#### includes documented count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_documented = md.contains("**Documented:** 75")
expect(has_documented).to_equal(true)
```

</details>

#### includes missing docs count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_missing = md.contains("**Missing Docs:** 25")
expect(has_missing).to_equal(true)
```

</details>

#### includes overall status indicator

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_status = md.contains("**Overall Status:**")
expect(has_status).to_equal(true)
```

</details>

#### includes sdoctest coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_sdoctest = md.contains("**SDoctest Coverage:**")
expect(has_sdoctest).to_equal(true)
```

</details>

### generate_coverage_markdown scope breakdown

#### includes scope table

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_table = md.contains("| Scope | Files | Items | Documented | Coverage % |")
expect(has_table).to_equal(true)
```

</details>

#### includes table separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_separator = md.contains("|-------|-------|-------|------------|-----------|")
expect(has_separator).to_equal(true)
```

</details>

#### groups files by scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_table = md.contains("| File | Missing Docs | Total Items | Coverage % |")
expect(has_table).to_equal(true)
```

</details>

#### lists files with missing docs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_parser = md.contains("parser.spl")
expect(has_parser).to_equal(true)
```

</details>

#### shows file paths in code blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_code_block = md.contains("`")
expect(has_code_block).to_equal(true)
```

</details>

### generate_coverage_markdown missing sdoctests

#### includes functions table

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_table = md.contains("| Function | File | Line |")
expect(has_table).to_equal(true)
```

</details>

#### lists functions without sdoctests

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_trim = md.contains("trim")
val has_parse = md.contains("parse")

expect(has_trim).to_equal(true)
expect(has_parse).to_equal(true)
```

</details>

#### shows line numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_h1 = md.contains("# ")
val has_h2 = md.contains("## ")

expect(has_h1).to_equal(true)
expect(has_h2).to_equal(true)
```

</details>

#### uses proper table syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_pipes = md.contains("|")
expect(has_pipes).to_equal(true)
```

</details>

#### uses proper bold syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_bold = md.contains("**")
expect(has_bold).to_equal(true)
```

</details>

#### uses proper code block syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_backticks = md.contains("`")
expect(has_backticks).to_equal(true)
```

</details>

### generate_coverage_markdown status indicators

#### shows status emoji for overall coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_emoji = md.contains("✅") or md.contains("⚠️") or md.contains("❌")
expect(has_emoji).to_equal(true)
```

</details>

### generate_coverage_markdown empty cases

#### handles report with no files

1. var report = CoverageReport create
   - Expected: has_summary is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = CoverageReport create
2. var file = FileCoverage create
   - Expected: has_structure is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report_with_files()
val md = generate_coverage_markdown(report)

val has_numbers = md.contains("100") and md.contains("75") and md.contains("25")
expect(has_numbers).to_equal(true)
```

</details>

#### produces valid markdown that could be rendered

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/doc_coverage/markdown_report_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
