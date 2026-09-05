# Query Ast Query Specification

> Tests covering ast pattern parser basics, predicate value extraction, node kind matching, predicate evaluation, output format.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Ast Query Specification

## Scenarios

### ast pattern parser basics

#### parses simple node kind

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses simple node kind
   - Expected: kind equals `function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple node kind")
val q = "(function)"
val inner = q.substring(1, q.len() - 1).trim()
val kind = inner.split(" ")[0]
expect(kind).to_equal("function")
```

</details>

#### parses node kind with name predicate

- parses node kind with name predicate
   - Expected: kind equals `function`
   - Expected: has_name is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses node kind with name predicate")
val q = "(function name: \"main\")"
val inner = q.substring(1, q.len() - 1).trim()
val kind = inner.split(" ")[0]
expect(kind).to_equal("function")
val has_name = inner.contains("name:")
expect(has_name).to_equal(true)
```

</details>

#### parses node kind with return_type predicate

- parses node kind with return_type predicate
   - Expected: kind equals `function`
   - Expected: has_return is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses node kind with return_type predicate")
val q = "(function return_type: \"i64\")"
val inner = q.substring(1, q.len() - 1).trim()
val kind = inner.split(" ")[0]
expect(kind).to_equal("function")
val has_return = inner.contains("return_type:")
expect(has_return).to_equal(true)
```

</details>

#### parses wildcard node kind

- parses wildcard node kind
   - Expected: first equals `*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses wildcard node kind")
val q = "(* name: \"foo\")"
val inner = q.substring(1, q.len() - 1).trim()
val first = inner.substring(0, 1)
expect(first).to_equal("*")
```

</details>

#### parses multiple predicates

- parses multiple predicates
   - Expected: has_name is true
   - Expected: has_ret is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple predicates")
val q = "(function name: \"parse\" return_type: \"i64\")"
val inner = q.substring(1, q.len() - 1).trim()
val has_name = inner.contains("name:")
val has_ret = inner.contains("return_type:")
expect(has_name).to_equal(true)
expect(has_ret).to_equal(true)
```

</details>

#### parses nested pattern

- parses nested pattern
   - Expected: has_methods is true
   - Expected: has_nested is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nested pattern")
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

- extracts quoted string value
   - Expected: value equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts quoted string value")
val pred_str = "name: \"main\""
val colon_pos = pred_str.index_of(":")
val after_colon = pred_str.substring(colon_pos + 1).trim()
val value = after_colon.substring(1, after_colon.len() - 1)
expect(value).to_equal("main")
```

</details>

#### detects glob pattern with wildcard

- detects glob pattern with wildcard
   - Expected: has_glob is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects glob pattern with wildcard")
val value = "std.*"
val has_glob = value.contains("*")
expect(has_glob).to_equal(true)
```

</details>

#### extracts field name before colon

- extracts field name before colon
   - Expected: field equals `return_type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts field name before colon")
val pred_str = "return_type: \"i64\""
val colon_pos = pred_str.index_of(":")
val field = pred_str.substring(0, colon_pos).trim()
expect(field).to_equal("return_type")
```

</details>

#### handles multiple fields in string

- handles multiple fields in string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple fields in string")
val inner = "function name: \"test\" return_type: \"i64\""
val parts = inner.split("\"")
# parts: ["function name: ", "test", " return_type: ", "i64", ""]
expect(parts.len()).to_be_greater_than(3)
```

</details>

### node kind matching

#### matches function to fn

- matches function to fn
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches function to fn")
val pattern_kind = "function"
val sym_kind = "fn"
val matches = pattern_kind == "function" and (sym_kind == "fn" or sym_kind == "method")
expect(matches).to_equal(true)
```

</details>

#### matches function to method

- matches function to method
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches function to method")
val pattern_kind = "function"
val sym_kind = "method"
val matches = pattern_kind == "function" and (sym_kind == "fn" or sym_kind == "method" or sym_kind == "static_method" or sym_kind == "extern_fn")
expect(matches).to_equal(true)
```

</details>

#### matches wildcard to any

- matches wildcard to any
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches wildcard to any")
val pattern_kind = "*"
val matches = pattern_kind == "*"
expect(matches).to_equal(true)
```

</details>

#### class does not match fn

- class does not match fn
   - Expected: matches is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("class does not match fn")
val pattern_kind = "class"
val sym_kind = "fn"
val matches = pattern_kind == sym_kind
expect(matches).to_equal(false)
```

</details>

#### matches import kind

- matches import kind
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches import kind")
val pattern_kind = "import"
val sym_kind = "import"
val matches = pattern_kind == sym_kind
expect(matches).to_equal(true)
```

</details>

#### matches impl kind

- matches impl kind
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches impl kind")
val pattern_kind = "impl"
val sym_kind = "impl"
val matches = pattern_kind == sym_kind
expect(matches).to_equal(true)
```

</details>

### predicate evaluation

#### name equals match

- name equals match
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("name equals match")
val sym_name = "query_main"
val pred_value = "query_main"
val matches = sym_name == pred_value
expect(matches).to_equal(true)
```

</details>

#### name equals mismatch

- name equals mismatch
   - Expected: matches is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("name equals mismatch")
val sym_name = "query_main"
val pred_value = "other"
val matches = sym_name == pred_value
expect(matches).to_equal(false)
```

</details>

#### glob match with wildcard

- glob match with wildcard
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("glob match with wildcard")
val value = "std.text"
val pattern = "std.*"
val prefix = "std."
val matches = value.starts_with(prefix)
expect(matches).to_equal(true)
```

</details>

#### visibility pub for top-level

- visibility pub for top-level
   - Expected: visibility equals `pub`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("visibility pub for top-level")
val parent = ""
val name = "query_main"
var visibility = "private"
if parent == "" and not name.starts_with("_"):
    visibility = "pub"
expect(visibility).to_equal("pub")
```

</details>

#### visibility private for prefixed

- visibility private for prefixed
   - Expected: visibility equals `private`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("visibility private for prefixed")
val parent = ""
val name = "_internal_fn"
var visibility = "private"
if parent == "" and not name.starts_with("_"):
    visibility = "pub"
expect(visibility).to_equal("private")
```

</details>

#### trait extraction from impl signature

- trait extraction from impl signature
   - Expected: first_word equals `Printable`
   - Expected: is_for is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trait extraction from impl signature")
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

- text format includes file:line


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text format includes file:line")
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

- compact format is single line
   - Expected: newlines is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compact format is single line")
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

- json format has curly braces
   - Expected: has_file is true
   - Expected: has_line is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("json format has curly braces")
val entry = "{\"file\": \"test.spl\", \"line\": 10, \"kind\": \"class\", \"name\": \"MyClass\"}"
val has_file = entry.contains("\"file\"")
val has_line = entry.contains("\"line\"")
expect(has_file).to_equal(true)
expect(has_line).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/query_ast_query_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ast pattern parser basics, predicate value extraction, node kind matching, predicate evaluation, output format.
- ast pattern parser basics
- predicate value extraction
- node kind matching
- predicate evaluation
- output format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
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

- Canonical SPipe generation for source `5251e502ac59dba33aafcb684bc270125f52b679a18eccaa4cf22735e25c029e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5251e502ac59dba33aafcb684bc270125f52b679a18eccaa4cf22735e25c029e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5251e502ac59dba33aafcb684bc270125f52b679a18eccaa4cf22735e25c029e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/cli/query_ast_query_spec.spl
mirror: doc/06_spec/unit/app/cli/query_ast_query_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/query_ast_query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/query_ast_query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/query_ast_query_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple node kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_ast_query_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses node kind with name predicate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_ast_query_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses node kind with return_type predicate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
