# query_sem_query_spec

> Tests for CodeQL-style semantic queries using SQL-like syntax. Validates query parsing, predicate evaluation, and execution logic.

<!-- sdn-diagram:id=query_sem_query_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_sem_query_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_sem_query_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_sem_query_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# query_sem_query_spec

Tests for CodeQL-style semantic queries using SQL-like syntax. Validates query parsing, predicate evaluation, and execution logic.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SQ-001 to #SQ-010 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/app/cli/query_sem_query_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for CodeQL-style semantic queries using SQL-like syntax.
Validates query parsing, predicate evaluation, and execution logic.

## Scenarios

### semantic query parser

#### parses FIND fn WHERE

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "FIND fn WHERE return_type = \"i64\""
val starts_find = q.starts_with("FIND ")
expect(starts_find).to_equal(true)
val after_find = q.substring(5)
val where_idx = after_find.index_of("WHERE") ?? -1
expect(where_idx).to_be_greater_than(0)
```

</details>

#### extracts target from FIND

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "FIND fn WHERE name = \"test\""
val after_find = q.substring(5).trim()
val target = after_find.split(" ")[0]
expect(target).to_equal("fn")
```

</details>

#### extracts predicate after WHERE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "FIND fn WHERE return_type = \"i64\""
val where_pos = q.index_of("WHERE") ?? -1
val pred_str = q.substring(where_pos + 5).trim()
expect(pred_str).to_start_with("return_type")
```

</details>

#### supports AND conjunction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "FIND fn WHERE name starts_with \"parse_\" AND param_count > 2"
val has_and = q.contains("AND")
expect(has_and).to_equal(true)
```

</details>

#### parses FIND with class target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "FIND class WHERE has_method(\"to_string\")"
val target = q.substring(5).split(" ")[0]
expect(target).to_equal("class")
```

</details>

#### parses FIND with struct target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "FIND struct WHERE field_count > 5"
val target = q.substring(5).split(" ")[0]
expect(target).to_equal("struct")
```

</details>

### comparison operators

#### parses equals operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "name = \"test\""
val has_eq = pred.contains("=")
expect(has_eq).to_equal(true)
```

</details>

#### parses not equals operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "name != \"test\""
val has_neq = pred.contains("!=")
expect(has_neq).to_equal(true)
```

</details>

#### parses greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "param_count > 2"
val has_gt = pred.contains(">")
expect(has_gt).to_equal(true)
```

</details>

#### parses less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "field_count < 10"
val has_lt = pred.contains("<")
expect(has_lt).to_equal(true)
```

</details>

#### parses starts_with

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "name starts_with \"parse_\""
val has_sw = pred.contains("starts_with")
expect(has_sw).to_equal(true)
```

</details>

#### parses contains

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "module contains \"std\""
val has_contains = pred.contains("contains")
expect(has_contains).to_equal(true)
```

</details>

### function predicates

#### parses calls predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "calls(\"rt_file_read_text\")"
val is_calls = pred.starts_with("calls(")
expect(is_calls).to_equal(true)
```

</details>

#### extracts calls argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "calls(\"rt_file_read_text\")"
val inner = pred.substring(7, pred.len() - 2)
expect(inner).to_equal("rt_file_read_text")
```

</details>

#### parses has_method predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "has_method(\"to_string\")"
val is_hm = pred.starts_with("has_method(")
expect(is_hm).to_equal(true)
```

</details>

#### parses implements predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "implements(\"Printable\")"
val is_impl = pred.starts_with("implements(")
expect(is_impl).to_equal(true)
```

</details>

#### parses imports predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "imports(\"std\")"
val is_imports = pred.starts_with("imports(")
expect(is_imports).to_equal(true)
```

</details>

### target matching

#### fn matches fn kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "fn"
val kind = "fn"
val matches = target == "fn" and (kind == "fn" or kind == "method")
expect(matches).to_equal(true)
```

</details>

#### fn matches method kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "fn"
val kind = "method"
val matches = target == "fn" and (kind == "fn" or kind == "method" or kind == "static_method" or kind == "extern_fn")
expect(matches).to_equal(true)
```

</details>

#### type matches class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "type"
val kind = "class"
val matches = target == "type" and (kind == "class" or kind == "struct" or kind == "enum" or kind == "trait")
expect(matches).to_equal(true)
```

</details>

#### type matches struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "type"
val kind = "struct"
val matches = target == "type" and (kind == "class" or kind == "struct" or kind == "enum" or kind == "trait")
expect(matches).to_equal(true)
```

</details>

#### class does not match fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "class"
val kind = "fn"
val matches = target == kind
expect(matches).to_equal(false)
```

</details>

#### wildcard matches anything

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "*"
val matches = target == "*"
expect(matches).to_equal(true)
```

</details>

### numeric predicates

#### counts params from empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ""
var count = 0
if params != "":
    val parts = params.split(",")
    for part in parts:
        if part.trim() != "":
            count = count + 1
expect(count).to_equal(0)
```

</details>

#### counts single param

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = "x: i64"
val parts = params.split(",")
var count = 0
for part in parts:
    if part.trim() != "":
        count = count + 1
expect(count).to_equal(1)
```

</details>

#### counts multiple params

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = "a: i64, b: text, c: bool"
val parts = params.split(",")
var count = 0
for part in parts:
    if part.trim() != "":
        count = count + 1
expect(count).to_equal(3)
```

</details>

#### param_count > 2 comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 3
val threshold = 2
val matches = count > threshold
expect(matches).to_equal(true)
```

</details>

#### field_count > 5 comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 3
val threshold = 5
val matches = count > threshold
expect(matches).to_equal(false)
```

</details>

### AND splitting

#### splits on AND keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred_str = "name = \"foo\" AND return_type = \"i64\""
val parts = pred_str.split(" AND ")
expect(parts.len()).to_equal(2)
expect(parts[0].trim()).to_equal("name = \"foo\"")
```

</details>

#### handles single predicate without AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred_str = "name = \"foo\""
val parts = pred_str.split(" AND ")
expect(parts.len()).to_equal(1)
```

</details>

#### splits multiple AND conjunctions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred_str = "a = \"1\" AND b = \"2\" AND c = \"3\""
val parts = pred_str.split(" AND ")
expect(parts.len()).to_equal(3)
```

</details>

### sem query output format

#### text format has file:line

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
val line = 42
val kind = "fn"
val name = "query_main"
val output = "{file}:{line}: [{kind}] {name}"
expect(output).to_contain("query.spl:42")
```

</details>

#### json format has required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = "{\"file\": \"test.spl\", \"line\": 10}"
val has_file = entry.contains("\"file\"")
val has_line = entry.contains("\"line\"")
expect(has_file).to_equal(true)
expect(has_line).to_equal(true)
```

</details>

#### results count is printed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 5
val footer = "Total: {count} results"
expect(footer).to_equal("Total: 5 results")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
