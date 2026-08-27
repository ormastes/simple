# Match Expression Separator Specification

> The runtime has two match parsers:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Expression Separator Specification

The runtime has two match parsers:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-ME-001 to #PARSER-ME-010 |
| Category | Infrastructure \| Parser |
| Status | In Progress |
| Source | `test/03_system/feature/usage/parser_match_expression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Bug: Match arm separators in expression context

The runtime has two match parsers:
1. Statement-level: `case` keyword + `:` (works, but no return value)
2. Expression-level: only `=>` works (returns value, rejects `:` and `case`)

The expression-level parser should also accept `:` and `case` keyword.
Fix: src/app/parser/expr/control.spl lines 78-94

Broken syntax (expression context):
use std.spec.step

val y = match x:
42: "found"           # error: expected FatArrow, found Colon
val y = match x:
case 42: "found"     # error: expected pattern, found Case

After rebuild, uncomment skipped tests in Group 3 below.

## Scenarios

### Match Statement case+colon

#### executes matching arm for integer patterns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes matching arm for integer patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes matching arm for integer patterns")
expect match_side_effect(0) == "zero"
expect match_side_effect(1) == "one"
expect match_side_effect(99) == "other"
```

</details>

#### executes arm with guard clauses

- executes arm with guard clauses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes arm with guard clauses")
expect match_guard_side_effect(-5) == "negative"
expect match_guard_side_effect(0) == "zero"
expect match_guard_side_effect(42) == "positive"
```

</details>

### Match Expression FatArrow

#### single-expression arms return values

- single-expression arms return values


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("single-expression arms return values")
val v1 = match 42:
    42 => "found"
    _ => "other"
expect v1 == "found"
val v2 = match 99:
    42 => "found"
    _ => "other"
expect v2 == "other"
```

</details>

#### multi-line arm bodies return last expression

- multi-line arm bodies return last expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multi-line arm bodies return last expression")
val output = match 42:
    42 =>
        val x = 42 + 1
        x
    _ =>
        0
expect output == 43
```

</details>

#### multiple statements in arm body

- multiple statements in arm body


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple statements in arm body")
val output = match 10:
    10 =>
        val a = 10 * 2
        val b = a + 5
        b
    _ =>
        -1
expect output == 25
```

</details>

#### guard clauses select correct arm

- guard clauses select correct arm


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("guard clauses select correct arm")
val output = match 42:
    x if x > 100 => "big"
    x if x > 0 => "positive"
    _ => "other"
expect output == "positive"
```

</details>

#### nested match expressions return values

- nested match expressions return values


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested match expressions return values")
val a = 1
val output = match a:
    1 =>
        val inner = match 2:
            2 => "one-two"
            _ => "one-other"
        inner
    _ =>
        "other"
expect output == "one-two"
```

</details>

### Match Statement-Expression Consistency

#### expression and statement match get same answers

- expression and statement match get same answers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expression and statement match get same answers")
val expr_val = match 42:
    42 => "found_expr"
    _ => "other_expr"
expect expr_val == "found_expr"
expect match_side_effect(0) == "zero"
```

</details>

#### expression match multi-line returns correct value

- expression match multi-line returns correct value


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expression match multi-line returns correct value")
val output = match 2:
    1 =>
        100
    2 =>
        200
    _ =>
        0
expect output == 200
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `912a54504ae26ac0cf65461a7c1babd4f1711aae673cc2ebad27e65b1cf7c8b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `912a54504ae26ac0cf65461a7c1babd4f1711aae673cc2ebad27e65b1cf7c8b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `912a54504ae26ac0cf65461a7c1babd4f1711aae673cc2ebad27e65b1cf7c8b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_match_expression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_match_expression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_match_expression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_match_expression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_match_expression_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes matching arm for integer patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_match_expression_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes arm with guard clauses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_match_expression_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-expression arms return values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
