# Json Export Specification

> <details>

<!-- sdn-diagram:id=json_export_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=json_export_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

json_export_spec -> std
json_export_spec -> doc_coverage
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=json_export_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Export Specification

## Scenarios

### export_coverage_json structure

#### generates valid JSON with summary section

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_summary = json.contains("\"summary\":")
expect(has_summary).to_equal(true)
```

</details>

#### includes total_items in summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_total = json.contains("\"total_items\": 10")
expect(has_total).to_equal(true)
```

</details>

#### includes documented_items in summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_documented = json.contains("\"documented_items\": 7")
expect(has_documented).to_equal(true)
```

</details>

#### includes missing_docs in summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_missing = json.contains("\"missing_docs\": 3")
expect(has_missing).to_equal(true)
```

</details>

#### includes sdoctest_coverage in summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_sdoc = json.contains("\"sdoctest_coverage\": 5")
expect(has_sdoc).to_equal(true)
```

</details>

#### includes overall_percent in summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_pct = json.contains("\"overall_percent\":")
expect(has_pct).to_equal(true)
```

</details>

#### includes timestamp in summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_timestamp = json.contains("\"timestamp\": 1640000000")
expect(has_timestamp).to_equal(true)
```

</details>

### export_coverage_json files array

#### includes files array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_files = json.contains("\"files\":")
expect(has_files).to_equal(true)
```

</details>

#### exports file coverage details

1. var report = create test report
   - Expected: has_file_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var report = create_test_report()
val file_cov = create_test_file_coverage("/src/std/test.spl")
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_file_path = json.contains("\"/src/std/test.spl\"")
expect(has_file_path).to_equal(true)
```

</details>

#### includes file total_items

1. var report = create test report
   - Expected: has_total is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var report = create_test_report()
val file_cov = create_test_file_coverage("/src/std/test.spl")
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_total = json.contains("\"total_items\": 3")
expect(has_total).to_equal(true)
```

</details>

#### handles multiple files

1. var report = create test report
   - Expected: has_test1 is true
   - Expected: has_test2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_name is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_kind is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_line is true
   - Expected: has_col is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_true is true
   - Expected: has_false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_tags is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_tags is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_excellent is true
   - Expected: has_complete is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_escaped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = create test report
2. var file cov = create test file coverage
   - Expected: has_escaped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var report = create_test_report()
var file_cov = create_test_file_coverage("/home/user\\path/test.spl")
report.files = [file_cov]

val json = export_coverage_json(report, false)

val has_escaped = json.contains("\\\\")
expect(has_escaped).to_equal(true)
```

</details>

#### handles newlines in signatures

1. var report = create test report
2. var file cov = create test file coverage
3. var item = DocItem create function
   - Expected: has_escaped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val starts_correctly = json.starts_with("{")
expect(starts_correctly).to_equal(true)
```

</details>

#### ends with closing brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val trimmed = json.trim()
val ends_correctly = trimmed.ends_with("}")
expect(ends_correctly).to_equal(true)
```

</details>

#### contains proper JSON structure markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = create_test_report()
val json = export_coverage_json(report, false)

val has_files = json.contains("\"files\": [")
expect(has_files).to_equal(true)
```

</details>

### export_coverage_json integration

#### exports complete report with all data

1. var report = create test report
2. var file cov = create test file coverage
3. var item1 = DocItem create function
4. var item2 = DocItem create function
   - Expected: has_summary is true
   - Expected: has_files is true
   - Expected: has_add is true
   - Expected: has_subtract is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/doc_coverage/json_export_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
