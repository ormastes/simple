# todo_parser_spec

> Purpose: Prove that TodoItem construction and field access.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# todo_parser_spec

Purpose: Prove that TodoItem construction and field access.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/todo_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that TodoItem construction and field access.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### TodoItem construction and field access

#### should construct TodoItem with all fields and access them

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should construct TodoItem with all fields and access them
- Verify: should construct TodoItem with all fields and access them
   - Expected: item.keyword equals `TODO`
   - Expected: item.area equals `runtime`
   - Expected: item.priority equals `P1`
   - Expected: item.description equals `Add GC optimization`
   - Expected: item.file equals `gc.spl`
   - Expected: item.line equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct TodoItem with all fields and access them")
step("Verify: should construct TodoItem with all fields and access them")
# @req: REQ-APP-TOOLING-001
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
expect(item.line).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### should construct TodoItem with FIXME keyword

- should construct TodoItem with FIXME keyword
- Verify: should construct TodoItem with FIXME keyword
   - Expected: item.keyword equals `FIXME`
   - Expected: item.area equals `parser`
   - Expected: item.priority equals `P0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct TodoItem with FIXME keyword")
step("Verify: should construct TodoItem with FIXME keyword")
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

- should construct TodoItem with issue number
- Verify: should construct TodoItem with issue number
   - Expected: item.issue.is_some is true
   - Expected: item.issue.unwrap equals `456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct TodoItem with issue number")
step("Verify: should construct TodoItem with issue number")
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

- should construct TodoItem with blocked issues
- Verify: should construct TodoItem with blocked issues
   - Expected: item.blocked.len equals `3`
   - Expected: item.blocked[0] equals `100`
   - Expected: item.blocked[1] equals `200`
   - Expected: item.blocked[2] equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct TodoItem with blocked issues")
step("Verify: should construct TodoItem with blocked issues")
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
expect(item.blocked.len).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(item.blocked[0]).to_equal("100")
expect(item.blocked[1]).to_equal("200")
expect(item.blocked[2]).to_equal("300")
```

</details>

#### should construct TodoItem with both issue and blocked

- should construct TodoItem with both issue and blocked
- Verify: should construct TodoItem with both issue and blocked
   - Expected: item.issue.is_some is true
   - Expected: item.blocked.len equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct TodoItem with both issue and blocked")
step("Verify: should construct TodoItem with both issue and blocked")
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
expect(item.blocked.len).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### ParseResult construction and field access

#### should construct empty ParseResult

- should construct empty ParseResult
- Verify: should construct empty ParseResult
   - Expected: result.todos.len equals `0`
   - Expected: result.errors.len equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct empty ParseResult")
step("Verify: should construct empty ParseResult")
val result = ParseResult {
    todos: [],
    errors: []
}
expect(result.todos.len).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.errors.len).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should construct ParseResult with todos

- should construct ParseResult with todos
- Verify: should construct ParseResult with todos
   - Expected: result.todos.len equals `1`
   - Expected: result.todos[0].description equals `Write more tests`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct ParseResult with todos")
step("Verify: should construct ParseResult with todos")
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
expect(result.todos.len).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.todos[0].description).to_equal("Write more tests")
```

</details>

### ParseError construction and field access

#### should construct ParseError with all fields

- should construct ParseError with all fields
- Verify: should construct ParseError with all fields
   - Expected: error.file equals `bad.spl`
   - Expected: error.line equals `42`
   - Expected: error.message contains `Invalid TODO format`
   - Expected: error.raw_text equals `# TODO: fix this`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct ParseError with all fields")
step("Verify: should construct ParseError with all fields")
val error = ParseError {
    file: "bad.spl",
    line: 42,
    message: "Invalid TODO format: missing [area][priority]",
    raw_text: "# TODO: fix this"
}
expect(error.file).to_equal("bad.spl")
expect(error.line).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(error.message.contains("Invalid TODO format")).to_equal(true)
expect(error.raw_text).to_equal("# TODO: fix this")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-TOOLING-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6313ed2c6d9b55809aef5f1526b797e1a02704578df91bed0afeabdf9f240792`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6313ed2c6d9b55809aef5f1526b797e1a02704578df91bed0afeabdf9f240792`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6313ed2c6d9b55809aef5f1526b797e1a02704578df91bed0afeabdf9f240792`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/tooling/todo_parser_spec.spl
mirror: doc/06_spec/unit/app/tooling/todo_parser_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/todo_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/todo_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/todo_parser_spec.spl:105:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct TodoItem with all fields and access them' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/todo_parser_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct TodoItem with all fields and access them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/todo_parser_spec.spl:130:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct TodoItem with FIXME keyword' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/todo_parser_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct TodoItem with FIXME keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/todo_parser_spec.spl:149:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct TodoItem with issue number' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/todo_parser_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct TodoItem with issue number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/todo_parser_spec.spl:167:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct TodoItem with blocked issues' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/todo_parser_spec.spl:187:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct TodoItem with both issue and blocked' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/todo_parser_spec.spl:215:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct empty ParseResult' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
