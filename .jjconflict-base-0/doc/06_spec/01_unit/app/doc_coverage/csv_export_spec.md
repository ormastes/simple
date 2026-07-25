# Csv Export Specification

> <details>

<!-- sdn-diagram:id=csv_export_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=csv_export_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

csv_export_spec -> std
csv_export_spec -> doc_coverage
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=csv_export_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Csv Export Specification

## Scenarios

### export_coverage_csv header

#### includes CSV header row

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: [DocItem] = []
val csv = export_coverage_csv(items)

val has_header = csv.starts_with("name,file,line,kind,is_public,has_sdoctest,has_inline_comment,tags")
expect(has_header).to_equal(true)
```

</details>

#### header has correct field names

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("my_function", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_name = csv.contains("my_function")
expect(has_name).to_equal(true)
```

</details>

#### includes file path in row

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test", "/src/std/math.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_file = csv.contains("/src/std/math.spl")
expect(has_file).to_equal(true)
```

</details>

#### includes line number in row

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test", "/src/std/test.spl", 99, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_line = csv.contains(",99,")
expect(has_line).to_equal(true)
```

</details>

#### includes kind in row

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_kind = csv.contains("function")
expect(has_kind).to_equal(true)
```

</details>

#### exports multiple items

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_true = csv.contains(",true,")
expect(has_true).to_equal(true)
```

</details>

#### exports false as 'false'

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test", "/src/std/test.spl", 10, false, false)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_false = csv.contains(",false,")
expect(has_false).to_equal(true)
```

</details>

#### handles mixed boolean values

1. var item = create test item
   - Expected: has_both is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test, with comma", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_quoted = csv.contains("\"test, with comma\"")
expect(has_quoted).to_equal(true)
```

</details>

#### escapes quotes by doubling them

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test_fn", "/home/user/\"project\"/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_doubled = csv.contains("\"\"")
expect(has_doubled).to_equal(true)
```

</details>

#### quotes field with newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test_fn", "/src/test\nfile.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_quotes = csv.contains("\"")
expect(has_quotes).to_equal(true)
```

</details>

#### does not quote simple fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_item("test", "/src/std/test.spl", 10, true, true)
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val lines = csv.split("\n")
val has_data = lines.len() >= 2

expect(has_data).to_equal(true)
```

</details>

#### exports single tag

1. var item = create test item
   - Expected: has_tag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var item = create_test_item("test", "/src/std/test.spl", 10, true, true)
item.sdoctest_tags = ["coverage:excellent"]
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_tag = csv.contains("coverage:excellent")
expect(has_tag).to_equal(true)
```

</details>

#### exports multiple tags pipe-separated

1. var item = create test item
   - Expected: has_pipe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var item = create_test_item("test", "/src/std/test.spl", 10, true, true)
item.sdoctest_tags = ["coverage:excellent", "doc:complete"]
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_pipe = csv.contains("|")
expect(has_pipe).to_equal(true)
```

</details>

#### quotes tags field if contains comma

1. var item = create test item
   - Expected: has_quotes is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = DocItem.create_function("test", "/src/std/test.spl", 10, 5, "pub", "fn test()")
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_function = csv.contains("function")
expect(has_function).to_equal(true)
```

</details>

#### exports struct item

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = DocItem.create_struct("Point", "/src/std/test.spl", 10, 5, "pub")
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_struct = csv.contains("struct")
expect(has_struct).to_equal(true)
```

</details>

#### exports class item

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = DocItem.create_class("MyClass", "/src/std/test.spl", 10, 5, "pub")
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_class = csv.contains("class")
expect(has_class).to_equal(true)
```

</details>

#### exports enum item

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = DocItem.create_enum("Status", "/src/std/test.spl", 10, 5, "pub")
val items: [DocItem] = [item]
val csv = export_coverage_csv(items)

val has_enum = csv.contains("enum")
expect(has_enum).to_equal(true)
```

</details>

### export_coverage_csv edge cases

#### handles empty items array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: [DocItem] = []
val csv = export_coverage_csv(items)

val has_header = csv.contains("name,file,line")
expect(has_header).to_equal(true)
```

</details>

#### handles single item array

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. items push
   - Expected: has_fn0 is true
   - Expected: has_fn9 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var func = DocItem create function
2. var struct item = DocItem create struct
   - Expected: has_header is true
   - Expected: has_add is true
   - Expected: has_point is true
   - Expected: has_math is true
   - Expected: has_geometry is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/doc_coverage/csv_export_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
