# Branch Coverage 32 Specification

> Tests covering Complex String Interpolation, String Concatenation Chains, String Method Chains, String Edge Cases, Special String Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 32 Specification

## Scenarios

### Complex String Interpolation

#### multiple interpolations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- multiple interpolations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple interpolations")
val x = 5
val y = 10
val z = 15
val s = "{x} + {y} + {z}"
check(s.contains("5"))
check(s.contains("10"))
check(s.contains("15"))
```

</details>

#### interpolation with expressions

- interpolation with expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolation with expressions")
val a = 3
val b = 4
val result = "{a * b}"
check(result.contains("12"))
```

</details>

#### nested expression interpolation

- nested expression interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested expression interpolation")
val x = 2
val y = 3
val complex = "{x * (y + 1)}"
check(complex.contains("8"))
```

</details>

#### interpolation with method calls

- interpolation with method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolation with method calls")
val s = "hello"
val msg = "Length is {s.len()}"
check(msg.contains("5"))
```

</details>

### String Concatenation Chains

#### multiple concat

- multiple concat


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple concat")
val s1 = "a" + "b" + "c"
check(s1 == "abc")
```

</details>

#### long concat chain

- long concat chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("long concat chain")
val s2 = "a" + "b" + "c" + "d" + "e"
check(s2 == "abcde")
```

</details>

#### concat with variables

- concat with variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concat with variables")
val x = "hello"
val y = "world"
val z = x + " " + y
check(z == "hello world")
```

</details>

#### concat in expression

- concat in expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concat in expression")
val a = "test"
val b = ("x" + "y") + ("z")
check(b == "xyz")
```

</details>

### String Method Chains

#### trim and operations

- trim and operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trim and operations")
val s = "  hello  "
val clean = s.trim()
check(clean == "hello")
```

</details>

#### multiple replacements

- multiple replacements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple replacements")
val text = "abc"
val r1 = text.replace("a", "x")
val r2 = r1.replace("b", "y")
check(r2 == "xyc")
```

</details>

#### slice operations

- slice operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slice operations")
val s = "abcdefgh"
val sub = s[2..5]
check(sub.len() == 3)
```

</details>

### String Edge Cases

#### empty interpolation

- empty interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty interpolation")
val s = "{0}"
check(s.contains("0"))
```

</details>

#### consecutive interpolations

- consecutive interpolations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("consecutive interpolations")
val x = 1
val y = 2
val s = "{x}{y}"
check(s.contains("1"))
check(s.contains("2"))
```

</details>

#### interpolation at start

- interpolation at start


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolation at start")
val x = 5
val s = "{x} is the value"
check(s.starts_with("5"))
```

</details>

#### interpolation at end

- interpolation at end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolation at end")
val x = 5
val s = "Value is {x}"
check(s.ends_with("5"))
```

</details>

### Special String Cases

#### multiline string

- multiline string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiline string")
val s = """line1
```

</details>

#### raw string

- raw string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raw string")
val r = r"no {interpolation}"
check(r.contains("{"))
```

</details>

#### escaped characters

- escaped characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escaped characters")
val e = "line1\nline2"
check(e.contains("\n"))
```

</details>

#### string with quotes

- string with quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string with quotes")
val q = "He said \"hello\""
check(q.contains("\""))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/branch_coverage_32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Complex String Interpolation, String Concatenation Chains, String Method Chains, String Edge Cases, Special String Cases.
- Complex String Interpolation
- String Concatenation Chains
- String Method Chains
- String Edge Cases
- Special String Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `58bc898d8c013d659792f5f847edc4e02b8d667b58ddca6dfa4aa5ecd8ed2239`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58bc898d8c013d659792f5f847edc4e02b8d667b58ddca6dfa4aa5ecd8ed2239`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58bc898d8c013d659792f5f847edc4e02b8d667b58ddca6dfa4aa5ecd8ed2239`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler_core/branch_coverage_32_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/branch_coverage_32_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/branch_coverage_32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/branch_coverage_32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/branch_coverage_32_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple interpolations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/branch_coverage_32_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interpolation with expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/branch_coverage_32_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nested expression interpolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
