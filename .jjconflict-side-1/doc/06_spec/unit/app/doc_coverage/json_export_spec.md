# Json Export Specification

> Tests covering export_coverage_json structure, export_coverage_json files array, export_coverage_json item details, export_coverage_json tags inclusion, export_coverage_json escaping, export_coverage_json validity, export_coverage_json integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Export Specification

## Scenarios

### export_coverage_json structure

#### generates valid JSON with summary section

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates valid JSON with summary section
   - Expected: has_summary is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates valid JSON with summary section")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_summary = json.contains("\"summary\":")
expect(has_summary).to_equal(true)
```

</details>

#### includes total_items in summary

- includes total_items in summary
   - Expected: has_total is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes total_items in summary")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_total = json.contains("\"total_items\": 10")
expect(has_total).to_equal(true)
```

</details>

#### includes documented_items in summary

- includes documented_items in summary
   - Expected: has_documented is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes documented_items in summary")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_documented = json.contains("\"documented_items\": 7")
expect(has_documented).to_equal(true)
```

</details>

#### includes missing_docs in summary

- includes missing_docs in summary
   - Expected: has_missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes missing_docs in summary")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_missing = json.contains("\"missing_docs\": 3")
expect(has_missing).to_equal(true)
```

</details>

#### includes sdoctest_coverage in summary

- includes sdoctest_coverage in summary
   - Expected: has_sdoc is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes sdoctest_coverage in summary")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_sdoc = json.contains("\"sdoctest_coverage\": 5")
expect(has_sdoc).to_equal(true)
```

</details>

#### includes overall_percent in summary

- includes overall_percent in summary
   - Expected: has_pct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes overall_percent in summary")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_pct = json.contains("\"overall_percent\":")
expect(has_pct).to_equal(true)
```

</details>

#### includes timestamp in summary

- includes timestamp in summary
   - Expected: has_timestamp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes timestamp in summary")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_timestamp = json.contains("\"timestamp\": 1640000000")
expect(has_timestamp).to_equal(true)
```

</details>

### export_coverage_json files array

#### includes files array

- includes files array
   - Expected: has_files is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes files array")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_files = json.contains("\"files\":")
expect(has_files).to_equal(true)
```

</details>

#### exports file coverage details

- exports file coverage details
   - Expected: has_file_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports file coverage details")
var report = create_test_report()
val file_cov = create_test_file_coverage("/src/std/test.spl")
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_file_path = json.contains("\"/src/std/test.spl\"")
expect(has_file_path).to_equal(true)
```

</details>

#### includes file total_items

- includes file total_items
   - Expected: has_total is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes file total_items")
var report = create_test_report()
val file_cov = create_test_file_coverage("/src/std/test.spl")
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_total = json.contains("\"total_items\": 3")
expect(has_total).to_equal(true)
```

</details>

#### handles multiple files

- handles multiple files
   - Expected: has_test1 is true
   - Expected: has_test2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple files")
var report = create_test_report()
val file1 = create_test_file_coverage("/src/std/test1.spl")
val file2 = create_test_file_coverage("/src/std/test2.spl")
report.files = [file1, file2]

val json = export_coverage_json(report, false)

val has_test1 = json.contains("test1.spl")
val has_test2 = json.contains("test2.spl")

expect(has_test1).to_equal(true)
expect(has_test2).to_equal(true)
```

</details>

### export_coverage_json item details

#### includes item name

- includes item name
   - Expected: has_name is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes item name")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("my_function", "/src/std/test.spl", 10, 5, "pub", "fn my_function()")
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_name = json.contains("\"name\": \"my_function\"")
expect(has_name).to_equal(true)
```

</details>

#### includes item kind

- includes item kind
   - Expected: has_kind is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes item kind")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("test", "/src/std/test.spl", 10, 5, "pub", "fn test()")
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_kind = json.contains("\"kind\": \"function\"")
expect(has_kind).to_equal(true)
```

</details>

#### includes line and column numbers

- includes line and column numbers
   - Expected: has_line is true
   - Expected: has_col is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes line and column numbers")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("test", "/src/std/test.spl", 42, 8, "pub", "fn test()")
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_line = json.contains("\"line\": 42")
val has_col = json.contains("\"col\": 8")

expect(has_line).to_equal(true)
expect(has_col).to_equal(true)
```

</details>

#### includes boolean flags as JSON booleans

- includes boolean flags as JSON booleans
   - Expected: has_true is true
   - Expected: has_false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes boolean flags as JSON booleans")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("test", "/src/std/test.spl", 10, 5, "pub", "fn test()")
item.is_public = true
item.has_inline_comment = false
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_true = json.contains("\"is_public\": true")
val has_false = json.contains("\"has_inline_comment\": false")

expect(has_true).to_equal(true)
expect(has_false).to_equal(true)
```

</details>

### export_coverage_json tags inclusion

#### excludes tags when include_tags is false

- excludes tags when include_tags is false
   - Expected: has_tags is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes tags when include_tags is false")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("test", "/src/std/test.spl", 10, 5, "pub", "fn test()")
item.sdoctest_tags = ["tag1", "tag2"]
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_tags = json.contains("\"tags\":")
expect(has_tags).to_equal(false)
```

</details>

#### includes tags when include_tags is true

- includes tags when include_tags is true
   - Expected: has_tags is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes tags when include_tags is true")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("test", "/src/std/test.spl", 10, 5, "pub", "fn test()")
item.sdoctest_tags = ["tag1", "tag2"]
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, true)

val has_tags = json.contains("\"tags\":")
expect(has_tags).to_equal(true)
```

</details>

#### exports tag array correctly

- exports tag array correctly
   - Expected: has_excellent is true
   - Expected: has_complete is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports tag array correctly")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("test", "/src/std/test.spl", 10, 5, "pub", "fn test()")
item.sdoctest_tags = ["coverage:excellent", "doc:complete"]
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, true)

val has_excellent = json.contains("\"coverage:excellent\"")
val has_complete = json.contains("\"doc:complete\"")

expect(has_excellent).to_equal(true)
expect(has_complete).to_equal(true)
```

</details>

### export_coverage_json escaping

#### escapes quotes in strings

- escapes quotes in strings
   - Expected: has_escaped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes quotes in strings")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("test_\"quoted\"", "/src/std/test.spl", 10, 5, "pub", "fn test()")
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_escaped = json.contains("\\\"")
expect(has_escaped).to_equal(true)
```

</details>

#### escapes backslashes in strings

- escapes backslashes in strings
   - Expected: has_escaped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes backslashes in strings")
var report = create_test_report()
var file_cov = create_test_file_coverage("/home/user\\path/test.spl")
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_escaped = json.contains("\\\\")
expect(has_escaped).to_equal(true)
```

</details>

#### handles newlines in signatures

- handles newlines in signatures
   - Expected: has_escaped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles newlines in signatures")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/test.spl")

var item = DocItem.create_function("test", "/src/std/test.spl", 10, 5, "pub", "fn test()\n-> i64")
file_cov.items = [item]
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_escaped = json.contains("\\n")
expect(has_escaped).to_equal(true)
```

</details>

### export_coverage_json validity

#### starts with opening brace

- starts with opening brace
   - Expected: starts_correctly is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with opening brace")
val report = create_test_report()
val json = export_coverage_json(report, false)

val starts_correctly = json.starts_with("{")
expect(starts_correctly).to_equal(true)
```

</details>

#### ends with closing brace

- ends with closing brace
   - Expected: ends_correctly is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with closing brace")
val report = create_test_report()
val json = export_coverage_json(report, false)

val trimmed = json.trim()
val ends_correctly = trimmed.ends_with("}")
expect(ends_correctly).to_equal(true)
```

</details>

#### contains proper JSON structure markers

- contains proper JSON structure markers
   - Expected: has_colons is true
   - Expected: has_commas is true
   - Expected: has_braces is true
   - Expected: has_brackets is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains proper JSON structure markers")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_colons = json.contains(":")
val has_commas = json.contains(",")
val has_braces = json.contains("{") and json.contains("}")
val has_brackets = json.contains("[") and json.contains("]")

expect(has_colons).to_equal(true)
expect(has_commas).to_equal(true)
expect(has_braces).to_equal(true)
expect(has_brackets).to_equal(true)
```

</details>

#### handles empty files array

- handles empty files array
   - Expected: has_files is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty files array")
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_files = json.contains("\"files\": [")
expect(has_files).to_equal(true)
```

</details>

### export_coverage_json integration

#### exports complete report with all data

- exports complete report with all data
   - Expected: has_summary is true
   - Expected: has_files is true
   - Expected: has_add is true
   - Expected: has_subtract is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports complete report with all data")
var report = create_test_report()
var file_cov = create_test_file_coverage("/src/std/math.spl")

var item1 = DocItem.create_function("add", "/src/std/math.spl", 10, 5, "pub", "fn add(a: i64, b: i64) -> i64")
item1.is_public = true
item1.has_inline_comment = true
item1.has_sdoctest = true

var item2 = DocItem.create_function("subtract", "/src/std/math.spl", 20, 5, "pub", "fn subtract(a: i64, b: i64) -> i64")
item2.is_public = true
item2.has_inline_comment = false
item2.has_sdoctest = false

file_cov.items = [item1, item2]
report.files = [file_cov]

val json = export_coverage_json(report, true)

val has_summary = json.contains("\"summary\":")
val has_files = json.contains("\"files\":")
val has_add = json.contains("\"add\"")
val has_subtract = json.contains("\"subtract\"")

expect(has_summary).to_equal(true)
expect(has_files).to_equal(true)
expect(has_add).to_equal(true)
expect(has_subtract).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/doc_coverage/json_export_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering export_coverage_json structure, export_coverage_json files array, export_coverage_json item details, export_coverage_json tags inclusion, export_coverage_json escaping, export_coverage_json validity, export_coverage_json integration.
- export_coverage_json structure
- export_coverage_json files array
- export_coverage_json item details
- export_coverage_json tags inclusion
- export_coverage_json escaping
- export_coverage_json validity
- export_coverage_json integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `4ca6a9ac504dc25ad2aece44d9198b08dbb4e609d9c5b97ba24eb196acb69e09`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ca6a9ac504dc25ad2aece44d9198b08dbb4e609d9c5b97ba24eb196acb69e09`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ca6a9ac504dc25ad2aece44d9198b08dbb4e609d9c5b97ba24eb196acb69e09`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/doc_coverage/json_export_spec.spl
mirror: doc/06_spec/unit/app/doc_coverage/json_export_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/doc_coverage/json_export_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/doc_coverage/json_export_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/doc_coverage/json_export_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates valid JSON with summary section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/json_export_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes total_items in summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/json_export_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes documented_items in summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
