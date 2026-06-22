# Todo Parser Specification

> 1. issue: Some

<!-- sdn-diagram:id=todo_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=todo_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

todo_parser_spec -> tooling
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=todo_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Todo Parser Specification

## Scenarios

### TodoItem construction and field access

#### should construct TodoItem with all fields and access them

1. issue: Some
   - Expected: item.keyword equals `TODO`
   - Expected: item.area equals `runtime`
   - Expected: item.priority equals `P1`
   - Expected: item.description equals `Add GC optimization`
   - Expected: item.file equals `gc.spl`
   - Expected: item.line equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = TodoItem {
    keyword: "TODO",
    area: "runtime",
    priority: "P1",
    description: "Add GC optimization",
    issue: Some("123"),
    blocked: ["456", "789"],
    file: "gc.spl",
    line: 42,
    raw_text: "# TODO: [runtime][P1] Add GC optimization [#123] [blocked:#456,#789]"
}

# Verify all fields are accessible and have correct values
expect(item.keyword).to_equal("TODO")
expect(item.area).to_equal("runtime")
expect(item.priority).to_equal("P1")
expect(item.description).to_equal("Add GC optimization")
expect(item.file).to_equal("gc.spl")
expect(item.line).to_equal(42)
```

</details>

#### should construct TodoItem with FIXME keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = TodoItem {
    keyword: "FIXME",
    area: "parser",
    priority: "P0",
    description: "Fix crash on invalid input",
    issue: nil,
    blocked: [],
    file: "parser.rs",
    line: 100,
    raw_text: "// FIXME: [parser][P0] Fix crash on invalid input"
}
expect(item.keyword).to_equal("FIXME")
expect(item.area).to_equal("parser")
expect(item.priority).to_equal("P0")
```

</details>

#### should construct TodoItem with issue number

1. issue: Some
   - Expected: item.issue.is_some is true
   - Expected: item.issue.unwrap equals `456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = TodoItem {
    keyword: "TODO",
    area: "compiler",
    priority: "P1",
    description: "Implement feature X",
    issue: Some("456"),
    blocked: [],
    file: "compiler.spl",
    line: 200,
    raw_text: "# TODO: [compiler][P1] Implement feature X [#456]"
}
expect(item.issue.is_some).to_equal(true)
expect(item.issue.unwrap).to_equal("456")
```

</details>

#### should construct TodoItem with blocked issues

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = TodoItem {
    keyword: "TODO",
    area: "codegen",
    priority: "P2",
    description: "Optimize code generation",
    issue: nil,
    blocked: ["100", "200", "300"],
    file: "codegen.spl",
    line: 50,
    raw_text: "# TODO: [codegen][P2] Optimize code generation [blocked:#100,#200,#300]"
}
expect(item.blocked.len).to_equal(3)
expect(item.blocked[0]).to_equal("100")
expect(item.blocked[1]).to_equal("200")
expect(item.blocked[2]).to_equal("300")
```

</details>

#### should construct TodoItem with both issue and blocked

1. issue: Some
   - Expected: item.issue.is_some is true
   - Expected: item.blocked.len equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = TodoItem {
    keyword: "FIXME",
    area: "stdlib",
    priority: "P1",
    description: "Add string methods",
    issue: Some("500"),
    blocked: ["600"],
    file: "text.spl",
    line: 75,
    raw_text: "# FIXME: [stdlib][P1] Add string methods [#500] [blocked:#600]"
}
expect(item.issue.is_some).to_equal(true)
expect(item.blocked.len).to_equal(1)
```

</details>

### ParseResult construction and field access

#### should construct empty ParseResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ParseResult {
    todos: [],
    errors: []
}
expect(result.todos.len).to_equal(0)
expect(result.errors.len).to_equal(0)
```

</details>

#### should construct ParseResult with todos

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = TodoItem {
    keyword: "TODO",
    area: "test",
    priority: "P3",
    description: "Write more tests",
    issue: nil,
    blocked: [],
    file: "test.spl",
    line: 1,
    raw_text: "# TODO: [test][P3] Write more tests"
}
val result = ParseResult {
    todos: [item],
    errors: []
}
expect(result.todos.len).to_equal(1)
expect(result.todos[0].description).to_equal("Write more tests")
```

</details>

### ParseError construction and field access

#### should construct ParseError with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = ParseError {
    file: "bad.spl",
    line: 42,
    message: "Invalid TODO format: missing [area][priority]",
    raw_text: "# TODO: fix this"
}
expect(error.file).to_equal("bad.spl")
expect(error.line).to_equal(42)
expect(error.message.contains("Invalid TODO format")).to_equal(true)
expect(error.raw_text).to_equal("# TODO: fix this")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/todo_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TodoItem construction and field access
- ParseResult construction and field access
- ParseError construction and field access

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
