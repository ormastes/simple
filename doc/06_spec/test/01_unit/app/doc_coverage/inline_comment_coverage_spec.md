# Inline Comment Coverage Specification

> <details>

<!-- sdn-diagram:id=inline_comment_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inline_comment_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inline_comment_coverage_spec -> app
inline_comment_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inline_comment_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Comment Coverage Specification

## Scenarios

### Inline Comment Coverage Analysis

### InlineCommentResult creation

#### creates a result with default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = InlineCommentResult.create("test_fn", "function", "test.spl", 10)
expect(result.item_name).to_equal("test_fn")
expect(result.item_kind).to_equal("function")
expect(result.file_path).to_equal("test.spl")
expect(result.line).to_equal(10)
expect(result.has_inline_comment == false)
expect(result.has_docstring == false)
expect(result.has_sdoctest == false)
expect(result.warning_level).to_equal("none")
```

</details>

### compute_inline_comment_coverage

#### analyzes file with documented function

1. file write
2. files push
   - Expected: first.item_name equals `documented_function`
   - Expected: first.item_kind equals `function`
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create test file
val test_file = "/tmp/test_doc_fn.spl"
val content = "# This is a comment\nfn documented_function():\n    pass\n"
file_write(test_file, content)

var files: [text] = []
files.push(test_file)

val results = compute_inline_comment_coverage(files)
expect(results.len()).to_be_greater_than(0)

# Check first result
val first = results[0]
expect(first.item_name).to_equal("documented_function")
expect(first.item_kind).to_equal("function")
expect(first.has_inline_comment == true)

# Cleanup
file_delete(test_file)
```

</details>

#### analyzes file with undocumented function

1. file write
2. files push
   - Expected: first.item_name equals `undocumented_function`
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_undoc_fn.spl"
val content = "fn undocumented_function():\n    pass\n"
file_write(test_file, content)

var files: [text] = []
files.push(test_file)

val results = compute_inline_comment_coverage(files)
expect(results.len()).to_be_greater_than(0)

val first = results[0]
expect(first.item_name).to_equal("undocumented_function")
expect(first.has_inline_comment == false)
file_delete(test_file)
```

</details>

#### analyzes file with docstring

1. "fn with docstring
2. file write
3. files push
   - Expected: first.item_name equals `with_docstring`
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_docstring_fn.spl"
val lines = [
    "fn with_docstring():",
    "    \"\"\"This is a docstring\"\"\"",
    "    pass"
]
val content = lines.join("\n")
file_write(test_file, content)

var files: [text] = []
files.push(test_file)

val results = compute_inline_comment_coverage(files)
expect(results.len()).to_be_greater_than(0)

val first = results[0]
expect(first.item_name).to_equal("with_docstring")
expect(first.has_docstring == true)

file_delete(test_file)
```

</details>

#### analyzes file with class declaration

1. file write
2. files push
   - Expected: first.item_name equals `TestClass`
   - Expected: first.item_kind equals `class`
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_class.spl"
val content = "# Class comment\nclass TestClass:\n    pass\n"
file_write(test_file, content)

var files: [text] = []
files.push(test_file)

val results = compute_inline_comment_coverage(files)
expect(results.len()).to_be_greater_than(0)

val first = results[0]
expect(first.item_name).to_equal("TestClass")
expect(first.item_kind).to_equal("class")
expect(first.has_inline_comment == true)

file_delete(test_file)
```

</details>

#### analyzes file with struct declaration

1. file write
2. files push
   - Expected: first.item_name equals `Point`
   - Expected: first.item_kind equals `struct`
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_struct.spl"
val content = "# Struct comment\nstruct Point:\n    x: i64\n"
file_write(test_file, content)

var files: [text] = []
files.push(test_file)

val results = compute_inline_comment_coverage(files)
expect(results.len()).to_be_greater_than(0)

val first = results[0]
expect(first.item_name).to_equal("Point")
expect(first.item_kind).to_equal("struct")
expect(first.has_inline_comment == true)

file_delete(test_file)
```

</details>

#### analyzes file with enum declaration

1. file write
2. files push
   - Expected: first.item_name equals `Status`
   - Expected: first.item_kind equals `enum`
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_enum.spl"
val content = "# Enum comment\nenum Status:\n    Active\n"
file_write(test_file, content)

var files: [text] = []
files.push(test_file)

val results = compute_inline_comment_coverage(files)
expect(results.len()).to_be_greater_than(0)

val first = results[0]
expect(first.item_name).to_equal("Status")
expect(first.item_kind).to_equal("enum")
expect(first.has_inline_comment == true)

file_delete(test_file)
```

</details>

#### handles non-existent file

1. files push
   - Expected: results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var files: [text] = []
files.push("/tmp/does_not_exist_12345.spl")

val results = compute_inline_comment_coverage(files)
expect(results.len()).to_equal(0)
```

</details>

#### analyzes multiple items in one file

1. "fn func1
2. "fn func2
3. file write
4. files push
   - Expected: results.len() equals `3`
5. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_multi.spl"
val lines = [
    "# Function 1",
    "fn func1():",
    "    pass",
    "",
    "fn func2():",
    "    pass",
    "",
    "# Class 1",
    "class MyClass:",
    "    pass"
]
val content = lines.join("\n")
file_write(test_file, content)

var files: [text] = []
files.push(test_file)

val results = compute_inline_comment_coverage(files)
expect(results.len()).to_equal(3)

file_delete(test_file)
```

</details>

### emit_missing_comment_warnings

#### generates warnings for missing docs

1. var r1 = InlineCommentResult create
2. results push
   - Expected: warnings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results: [InlineCommentResult] = []

var r1 = InlineCommentResult.create("undocumented_fn", "function", "test.spl", 10)
r1 = InlineCommentResult(
    item_name: r1.item_name,
    item_kind: r1.item_kind,
    file_path: r1.file_path,
    line: r1.line,
    has_inline_comment: false,
    has_docstring: false,
    has_sdoctest: false,
    warning_level: "error"
)
results.push(r1)

val warnings = emit_missing_comment_warnings(results)
expect(warnings.len()).to_equal(1)
expect(warnings[0]).to_contain("ERROR")
expect(warnings[0]).to_contain("undocumented_fn")
```

</details>

#### does not generate warnings for documented items

1. var r1 = InlineCommentResult create
2. results push
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results: [InlineCommentResult] = []

var r1 = InlineCommentResult.create("documented_fn", "function", "test.spl", 10)
r1 = InlineCommentResult(
    item_name: r1.item_name,
    item_kind: r1.item_kind,
    file_path: r1.file_path,
    line: r1.line,
    has_inline_comment: true,
    has_docstring: true,
    has_sdoctest: false,
    warning_level: "none"
)
results.push(r1)

val warnings = emit_missing_comment_warnings(results)
expect(warnings.len()).to_equal(0)
```

</details>

### generate_coverage_report

#### generates report with summary statistics

1. var r1 = InlineCommentResult create
2. results push
3. var r2 = InlineCommentResult create
4. results push


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results: [InlineCommentResult] = []

var r1 = InlineCommentResult.create("fn1", "function", "test.spl", 1)
r1 = InlineCommentResult(
    item_name: r1.item_name,
    item_kind: r1.item_kind,
    file_path: r1.file_path,
    line: r1.line,
    has_inline_comment: true,
    has_docstring: true,
    has_sdoctest: false,
    warning_level: "none"
)
results.push(r1)

var r2 = InlineCommentResult.create("fn2", "function", "test.spl", 2)
r2 = InlineCommentResult(
    item_name: r2.item_name,
    item_kind: r2.item_kind,
    file_path: r2.file_path,
    line: r2.line,
    has_inline_comment: false,
    has_docstring: false,
    has_sdoctest: false,
    warning_level: "error"
)
results.push(r2)

val report = generate_coverage_report(results)
expect(report).to_contain("# Inline Comment Coverage Report")
expect(report).to_contain("Total Items:")
expect(report).to_contain("With Inline Comments:")
expect(report).to_contain("With Docstrings:")
expect(report).to_contain("With Both:")
expect(report).to_contain("With Neither:")
```

</details>

#### includes details by warning level

1. var r1 = InlineCommentResult create
2. results push
3. var r2 = InlineCommentResult create
4. results push


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results: [InlineCommentResult] = []

var r1 = InlineCommentResult.create("error_fn", "function", "test.spl", 1)
r1 = InlineCommentResult(
    item_name: r1.item_name,
    item_kind: r1.item_kind,
    file_path: r1.file_path,
    line: r1.line,
    has_inline_comment: false,
    has_docstring: false,
    has_sdoctest: false,
    warning_level: "error"
)
results.push(r1)

var r2 = InlineCommentResult.create("warn_fn", "function", "src/std/test.spl", 2)
r2 = InlineCommentResult(
    item_name: r2.item_name,
    item_kind: r2.item_kind,
    file_path: r2.file_path,
    line: r2.line,
    has_inline_comment: true,
    has_docstring: false,
    has_sdoctest: false,
    warning_level: "warn"
)
results.push(r2)

val report = generate_coverage_report(results)
expect(report).to_contain("### Errors")
expect(report).to_contain("### Warnings")
expect(report).to_contain("error_fn")
expect(report).to_contain("warn_fn")
```

</details>

#### calculates percentages correctly

1. var r1 = InlineCommentResult create
2. results push
3. var r2 = InlineCommentResult create
4. results push
5. var r3 = InlineCommentResult create
6. results push
7. var r4 = InlineCommentResult create
8. results push


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results: [InlineCommentResult] = []

# Add 4 items: 3 with inline, 2 with docstring, 1 with both, 1 with neither
var r1 = InlineCommentResult.create("fn1", "function", "test.spl", 1)
r1 = InlineCommentResult(
    item_name: r1.item_name,
    item_kind: r1.item_kind,
    file_path: r1.file_path,
    line: r1.line,
    has_inline_comment: true,
    has_docstring: true,
    has_sdoctest: false,
    warning_level: "none"
)
results.push(r1)

var r2 = InlineCommentResult.create("fn2", "function", "test.spl", 2)
r2 = InlineCommentResult(
    item_name: r2.item_name,
    item_kind: r2.item_kind,
    file_path: r2.file_path,
    line: r2.line,
    has_inline_comment: true,
    has_docstring: false,
    has_sdoctest: false,
    warning_level: "warn"
)
results.push(r2)

var r3 = InlineCommentResult.create("fn3", "function", "test.spl", 3)
r3 = InlineCommentResult(
    item_name: r3.item_name,
    item_kind: r3.item_kind,
    file_path: r3.file_path,
    line: r3.line,
    has_inline_comment: true,
    has_docstring: false,
    has_sdoctest: false,
    warning_level: "warn"
)
results.push(r3)

var r4 = InlineCommentResult.create("fn4", "function", "test.spl", 4)
r4 = InlineCommentResult(
    item_name: r4.item_name,
    item_kind: r4.item_kind,
    file_path: r4.file_path,
    line: r4.line,
    has_inline_comment: false,
    has_docstring: false,
    has_sdoctest: false,
    warning_level: "error"
)
results.push(r4)

val report = generate_coverage_report(results)
# 3 out of 4 = 75% inline
# 1 out of 4 = 25% docstring
expect(report).to_contain("With Inline Comments:** 3")
expect(report).to_contain("With Docstrings:** 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/inline_comment_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Inline Comment Coverage Analysis
- InlineCommentResult creation
- compute_inline_comment_coverage
- emit_missing_comment_warnings
- generate_coverage_report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
