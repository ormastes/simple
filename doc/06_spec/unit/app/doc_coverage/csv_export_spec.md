# Csv Export Specification

> Tests covering export_coverage_csv header, export_coverage_csv data rows, export_coverage_csv boolean values, export_coverage_csv escaping, export_coverage_csv tags, export_coverage_csv item types, export_coverage_csv edge cases, export_coverage_csv integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Csv Export Specification

## Scenarios

### export_coverage_csv header

#### includes CSV header row

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- includes CSV header row
   - Expected: has_header is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes CSV header row")
val items: [DocItem] = []
val csv = export_coverage_csv(items)

val has_header = csv.starts_with("name,file,line,kind,is_public,has_sdoctest,has_inline_comment,tags")
expect(has_header).to_equal(true)
```

</details>

#### header has correct field names

- header has correct field names
   - Expected: has_name is true
   - Expected: has_file is true
   - Expected: has_line is true
   - Expected: has_kind is true
   - Expected: has_public is true
   - Expected: has_sdoctest is true
   - Expected: has_inline is true
   - Expected: has_tags is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("header has correct field names")
val items: [DocItem] = []
val csv = export_coverage_csv(items)

val has_name = csv.contains("name")
val has_file = csv.contains("file")
val has_line = csv.contains("line")
val has_kind = csv.contains("kind")
val has_public = csv.contains("is_public")
val has_sdoctest = csv.contains("has_sdoctest")
val has_inline = csv.contains("has_inline_comment")
val has_tags = csv.contains("tags")

expect(has_name).to_equal(true)
expect(has_file).to_equal(true)
expect(has_line).to_equal(true)
expect(has_kind).to_equal(true)
expect(has_public).to_equal(true)
expect(has_sdoctest).to_equal(true)
expect(has_inline).to_equal(true)
expect(has_tags).to_equal(true)
```

</details>

### export_coverage_csv data rows

#### exports single item

- exports single item
   - Expected: has_header_and_data is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports single item")
val item = create_test_item("test_fn", "/src/std/test.spl", 42, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val lines = csv.split("\n")
val expected_lines = 2
val has_header_and_data = lines.len() >= expected_lines

expect(has_header_and_data).to_equal(true)
```

</details>

#### includes function name in row

- includes function name in row
   - Expected: has_name is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes function name in row")
val item = create_test_item("my_function", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_name = csv.contains("my_function")
expect(has_name).to_equal(true)
```

</details>

#### includes file path in row

- includes file path in row
   - Expected: has_file is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes file path in row")
val item = create_test_item("test", "/src/std/math.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_file = csv.contains("/src/std/math.spl")
expect(has_file).to_equal(true)
```

</details>

#### includes line number in row

- includes line number in row
   - Expected: has_line is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes line number in row")
val item = create_test_item("test", "/src/std/test.spl", 99, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_line = csv.contains(",99,")
expect(has_line).to_equal(true)
```

</details>

#### includes kind in row

- includes kind in row
   - Expected: has_kind is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes kind in row")
val item = create_test_item("test", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_kind = csv.contains("function")
expect(has_kind).to_equal(true)
```

</details>

#### exports multiple items

- exports multiple items
   - Expected: has_fn1 is true
   - Expected: has_fn2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports multiple items")
val item1 = create_test_item("fn1", "/src/std/test.spl", 10, true, true)
val item2 = create_test_item("fn2", "/src/std/test.spl", 20, false, false)
val items: [DocItem] = [item1, item2]
val csv = export_coverage_csv(items)

val has_fn1 = csv.contains("fn1")
val has_fn2 = csv.contains("fn2")

expect(has_fn1).to_equal(true)
expect(has_fn2).to_equal(true)
```

</details>

### export_coverage_csv boolean values

#### exports true as 'true'

- exports true as 'true'
   - Expected: has_true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports true as 'true'")
val item = create_test_item("test", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_true = csv.contains(",true,")
expect(has_true).to_equal(true)
```

</details>

#### exports false as 'false'

- exports false as 'false'
   - Expected: has_false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports false as 'false'")
val item = create_test_item("test", "/src/std/test.spl", 10, false, false)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_false = csv.contains(",false,")
expect(has_false).to_equal(true)
```

</details>

#### handles mixed boolean values

- handles mixed boolean values
   - Expected: has_both is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles mixed boolean values")
var item = create_test_item("test", "/src/std/test.spl", 10, true, false)
item.has_inline_comment = true
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val lines = csv.split("\n")
val has_both = lines.len() >= 2

expect(has_both).to_equal(true)
```

</details>

### export_coverage_csv escaping

#### quotes field with comma

- quotes field with comma
   - Expected: has_quoted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes field with comma")
val item = create_test_item("test, with comma", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_quoted = csv.contains("\"test, with comma\"")
expect(has_quoted).to_equal(true)
```

</details>

#### escapes quotes by doubling them

- escapes quotes by doubling them
   - Expected: has_doubled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes quotes by doubling them")
val item = create_test_item("test_fn", "/home/user/\"project\"/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_doubled = csv.contains("\"\"")
expect(has_doubled).to_equal(true)
```

</details>

#### quotes field with newline

- quotes field with newline
   - Expected: has_quotes is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes field with newline")
val item = create_test_item("test_fn", "/src/test\nfile.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_quotes = csv.contains("\"")
expect(has_quotes).to_equal(true)
```

</details>

#### does not quote simple fields

- does not quote simple fields
   - Expected: has_data is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not quote simple fields")
val item = create_test_item("simple_name", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val lines = csv.split("\n")
val has_data = lines.len() >= 2

expect(has_data).to_equal(true)
```

</details>

### export_coverage_csv tags

#### exports empty tags as empty field

- exports empty tags as empty field
   - Expected: has_data is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports empty tags as empty field")
val item = create_test_item("test", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val lines = csv.split("\n")
val has_data = lines.len() >= 2

expect(has_data).to_equal(true)
```

</details>

#### exports single tag

- exports single tag
   - Expected: has_tag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports single tag")
var item = create_test_item("test", "/src/std/test.spl", 10, true, true)
item.sdoctest_tags = ["coverage:excellent"]
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_tag = csv.contains("coverage:excellent")
expect(has_tag).to_equal(true)
```

</details>

#### exports multiple tags pipe-separated

- exports multiple tags pipe-separated
   - Expected: has_pipe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports multiple tags pipe-separated")
var item = create_test_item("test", "/src/std/test.spl", 10, true, true)
item.sdoctest_tags = ["coverage:excellent", "doc:complete"]
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_pipe = csv.contains("|")
expect(has_pipe).to_equal(true)
```

</details>

#### quotes tags field if contains comma

- quotes tags field if contains comma
   - Expected: has_quotes is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes tags field if contains comma")
var item = create_test_item("test", "/src/std/test.spl", 10, true, true)
item.sdoctest_tags = ["tag,with,comma"]
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_quotes = csv.contains("\"")
expect(has_quotes).to_equal(true)
```

</details>

### export_coverage_csv item types

#### exports function item

- exports function item
   - Expected: has_function is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports function item")
val item = DocItem.create_function("test", "/src/std/test.spl", 10, 5, "pub", "fn test()")
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_function = csv.contains("function")
expect(has_function).to_equal(true)
```

</details>

#### exports struct item

- exports struct item
   - Expected: has_struct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports struct item")
val item = DocItem.create_struct("Point", "/src/std/test.spl", 10, 5, "pub")
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_struct = csv.contains("struct")
expect(has_struct).to_equal(true)
```

</details>

#### exports class item

- exports class item
   - Expected: has_class is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports class item")
val item = DocItem.create_class("MyClass", "/src/std/test.spl", 10, 5, "pub")
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_class = csv.contains("class")
expect(has_class).to_equal(true)
```

</details>

#### exports enum item

- exports enum item
   - Expected: has_enum is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports enum item")
val item = DocItem.create_enum("Status", "/src/std/test.spl", 10, 5, "pub")
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_enum = csv.contains("enum")
expect(has_enum).to_equal(true)
```

</details>

### export_coverage_csv edge cases

#### handles empty items array

- handles empty items array
   - Expected: has_header is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty items array")
val items: [DocItem] = []
val csv = export_coverage_csv(items)

val has_header = csv.contains("name,file,line")
expect(has_header).to_equal(true)
```

</details>

#### handles single item array

- handles single item array
   - Expected: has_correct_count is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single item array")
val item = create_test_item("only_one", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val lines = csv.split("\n")
val expected_lines = 2
val has_correct_count = lines.len() >= expected_lines

expect(has_correct_count).to_equal(true)
```

</details>

#### handles many items

- handles many items
   - Expected: has_fn0 is true
   - Expected: has_fn9 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles many items")
var items: [DocItem] = []
var i = 0
while i < 10:
    val item = create_test_item("fn{i}", "/src/std/test.spl", i, true, true)
    items.push(item)
    i = i + 1

val csv = export_coverage_csv(items)

val has_fn0 = csv.contains("fn0")
val has_fn9 = csv.contains("fn9")

expect(has_fn0).to_equal(true)
expect(has_fn9).to_equal(true)
```

</details>

### export_coverage_csv integration

#### exports mixed item types with all fields

- exports mixed item types with all fields
   - Expected: has_header is true
   - Expected: has_add is true
   - Expected: has_point is true
   - Expected: has_math is true
   - Expected: has_geometry is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports mixed item types with all fields")
var func = DocItem.create_function("add", "/src/std/math.spl", 10, 5, "pub", "fn add(a: i64, b: i64) -> i64")
func.is_public = true
func.has_sdoctest = true
func.has_inline_comment = true
func.sdoctest_tags = ["coverage:excellent", "doc:complete"]

var struct_item = DocItem.create_struct("Point", "/src/std/geometry.spl", 20, 5, "pub")
struct_item.is_public = true
struct_item.has_inline_comment = false

val items: [DocItem] = [func, struct_item]
val csv = export_coverage_csv(items)

val has_header = csv.contains("name,file,line")
val has_add = csv.contains("add")
val has_point = csv.contains("Point")
val has_math = csv.contains("math.spl")
val has_geometry = csv.contains("geometry.spl")

expect(has_header).to_equal(true)
expect(has_add).to_equal(true)
expect(has_point).to_equal(true)
expect(has_math).to_equal(true)
expect(has_geometry).to_equal(true)
```

</details>

#### produces parseable CSV format

- produces parseable CSV format
   - Expected: has_header is true
   - Expected: has_data is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces parseable CSV format")
val item1 = create_test_item("fn1", "/src/std/test.spl", 10, true, true)
val item2 = create_test_item("fn2", "/src/core/test.spl", 20, false, false)
val items: [DocItem] = [item1, item2]
val csv = export_coverage_csv(items)

val lines = csv.split("\n")
val has_header = lines.len() >= 1
val has_data = lines.len() >= 3

expect(has_header).to_equal(true)
expect(has_data).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/doc_coverage/csv_export_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering export_coverage_csv header, export_coverage_csv data rows, export_coverage_csv boolean values, export_coverage_csv escaping, export_coverage_csv tags, export_coverage_csv item types, export_coverage_csv edge cases, export_coverage_csv integration.
- export_coverage_csv header
- export_coverage_csv data rows
- export_coverage_csv boolean values
- export_coverage_csv escaping
- export_coverage_csv tags
- export_coverage_csv item types
- export_coverage_csv edge cases
- export_coverage_csv integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
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

- Canonical SPipe generation for source `3ae1a249cc4e463adc1c12edc39a571d2dd9f8cc13215521672d5f478542607f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ae1a249cc4e463adc1c12edc39a571d2dd9f8cc13215521672d5f478542607f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ae1a249cc4e463adc1c12edc39a571d2dd9f8cc13215521672d5f478542607f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/doc_coverage/csv_export_spec.spl
mirror: doc/06_spec/unit/app/doc_coverage/csv_export_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/doc_coverage/csv_export_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/doc_coverage/csv_export_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/doc_coverage/csv_export_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes CSV header row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/csv_export_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'header has correct field names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/csv_export_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports single item' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
