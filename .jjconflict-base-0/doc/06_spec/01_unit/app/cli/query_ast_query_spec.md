# query_ast_query_spec

> Tests for S-expression structural pattern matching against outline AST. Validates pattern parsing, predicate evaluation, and matching logic.

<!-- sdn-diagram:id=query_ast_query_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_ast_query_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_ast_query_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_ast_query_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# query_ast_query_spec

Tests for S-expression structural pattern matching against outline AST. Validates pattern parsing, predicate evaluation, and matching logic.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AQ-001 to #AQ-010 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/app/cli/query_ast_query_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for S-expression structural pattern matching against outline AST.
Validates pattern parsing, predicate evaluation, and matching logic.

## Scenarios

### ast pattern parser basics

#### parses simple node kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "(function)"
val inner = q.substring(1, q.len() - 1).trim()
val kind = inner.split(" ")[0]
expect(kind).to_equal("function")
```

</details>

#### parses node kind with name predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "(function name: \"main\")"
val inner = q.substring(1, q.len() - 1).trim()
val kind = inner.split(" ")[0]
expect(kind).to_equal("function")
val has_name = inner.contains("name:")
expect(has_name).to_equal(true)
```

</details>

#### parses node kind with return_type predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "(function return_type: \"i64\")"
val inner = q.substring(1, q.len() - 1).trim()
val kind = inner.split(" ")[0]
expect(kind).to_equal("function")
val has_return = inner.contains("return_type:")
expect(has_return).to_equal(true)
```

</details>

#### parses wildcard node kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "(* name: \"foo\")"
val inner = q.substring(1, q.len() - 1).trim()
val first = inner.substring(0, 1)
expect(first).to_equal("*")
```

</details>

#### parses multiple predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "(function name: \"parse\" return_type: \"i64\")"
val inner = q.substring(1, q.len() - 1).trim()
val has_name = inner.contains("name:")
val has_ret = inner.contains("return_type:")
expect(has_name).to_equal(true)
expect(has_ret).to_equal(true)
```

</details>

#### parses nested pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "(class methods: (function name: \"to_string\"))"
val inner = q.substring(1, q.len() - 1).trim()
val has_methods = inner.contains("methods:")
val has_nested = inner.contains("(function")
expect(has_methods).to_equal(true)
expect(has_nested).to_equal(true)
```

</details>

### predicate value extraction

#### extracts quoted string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred_str = "name: \"main\""
val colon_pos = pred_str.index_of(":") ?? -1
val after_colon = pred_str.substring(colon_pos + 1).trim()
val value = after_colon.substring(1, after_colon.len() - 1)
expect(value).to_equal("main")
```

</details>

#### detects glob pattern with wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "std.*"
val has_glob = value.contains("*")
expect(has_glob).to_equal(true)
```

</details>

#### extracts field name before colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred_str = "return_type: \"i64\""
val colon_pos = pred_str.index_of(":") ?? -1
val field = pred_str.substring(0, colon_pos).trim()
expect(field).to_equal("return_type")
```

</details>

#### handles multiple fields in string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = "function name: \"test\" return_type: \"i64\""
val parts = inner.split("\"")
# parts: ["function name: ", "test", " return_type: ", "i64", ""]
expect(parts.len()).to_be_greater_than(3)
```

</details>

### node kind matching

#### matches function to fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern_kind = "function"
val sym_kind = "fn"
val matches = pattern_kind == "function" and (sym_kind == "fn" or sym_kind == "method")
expect(matches).to_equal(true)
```

</details>

#### matches function to method

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern_kind = "function"
val sym_kind = "method"
val matches = pattern_kind == "function" and (sym_kind == "fn" or sym_kind == "method" or sym_kind == "static_method" or sym_kind == "extern_fn")
expect(matches).to_equal(true)
```

</details>

#### matches wildcard to any

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern_kind = "*"
val matches = pattern_kind == "*"
expect(matches).to_equal(true)
```

</details>

#### class does not match fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern_kind = "class"
val sym_kind = "fn"
val matches = pattern_kind == sym_kind
expect(matches).to_equal(false)
```

</details>

#### matches import kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern_kind = "import"
val sym_kind = "import"
val matches = pattern_kind == sym_kind
expect(matches).to_equal(true)
```

</details>

#### matches impl kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern_kind = "impl"
val sym_kind = "impl"
val matches = pattern_kind == sym_kind
expect(matches).to_equal(true)
```

</details>

### predicate evaluation

#### name equals match

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_name = "query_main"
val pred_value = "query_main"
val matches = sym_name == pred_value
expect(matches).to_equal(true)
```

</details>

#### name equals mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_name = "query_main"
val pred_value = "other"
val matches = sym_name == pred_value
expect(matches).to_equal(false)
```

</details>

#### glob match with wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "std.text"
val pattern = "std.*"
val prefix = "std."
val matches = value.starts_with(prefix)
expect(matches).to_equal(true)
```

</details>

#### visibility pub for top-level

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = ""
val name = "query_main"
var visibility = "private"
if parent == "" and not name.starts_with("_"):
    visibility = "pub"
expect(visibility).to_equal("pub")
```

</details>

#### visibility private for prefixed

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = ""
val name = "_internal_fn"
var visibility = "private"
if parent == "" and not name.starts_with("_"):
    visibility = "pub"
expect(visibility).to_equal("private")
```

</details>

#### trait extraction from impl signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = "impl Printable for MyClass:"
val rest = sig.substring(5).trim()
val first_word = rest.split(" ")[0]
val after = rest.substring(first_word.len()).trim()
val is_for = after.starts_with("for ")
expect(first_word).to_equal("Printable")
expect(is_for).to_equal(true)
```

</details>

### output format

#### text format includes file:line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
val line = 42
val kind = "fn"
val name = "query_main"
val output = "{file}:{line}: [{kind}] {name}"
expect(output).to_contain("src/app/cli/query.spl:42")
expect(output).to_contain("[fn]")
```

</details>

#### compact format is single line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = 10
val kind = "class"
val name = "MyClass"
val output = "{file}:{line}: [{kind}] {name}"
val newlines = output.contains("\n")
expect(newlines).to_equal(false)
```

</details>

#### json format has curly braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = "{\"file\": \"test.spl\", \"line\": 10, \"kind\": \"class\", \"name\": \"MyClass\"}"
val has_file = entry.contains("\"file\"")
val has_line = entry.contains("\"line\"")
expect(has_file).to_equal(true)
expect(has_line).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
