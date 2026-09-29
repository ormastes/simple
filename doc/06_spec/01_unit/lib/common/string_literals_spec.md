# String Literals Specification

> Tests covering text Literal Syntax.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Literals Specification

## Scenarios

### text Literal Syntax

#### double-quoted strings (interpolated by default)

#### creates simple string

- creates simple string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple string")
val s = "hello"
expect s == "hello"
```

</details>

#### supports escape sequences

- supports escape sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports escape sequences")
val s = "hello\nworld"
expect s.contains("\n") == true
```

</details>

#### supports expression interpolation

- supports expression interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports expression interpolation")
val result = "Sum: {1 + 2}"
expect result == "Sum: 3"
```

</details>

#### escapes braces with double braces

- escapes braces with double braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes braces with double braces")
val json = "{{key}}"
expect json == '{key}'  # Raw string for comparison
```

</details>

#### single-quoted strings (raw)

#### creates raw string

- creates raw string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates raw string")
val s = 'hello'
expect s == "hello"
```

</details>

#### preserves backslashes literally

- preserves backslashes literally


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves backslashes literally")
val s = 'hello\nworld'
expect s.contains("\\n") == true
```

</details>

#### preserves braces literally

- preserves braces literally


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves braces literally")
val s = '{name}'
expect s == '{name}'  # Raw string preserves {name} literally
```

</details>

#### is useful for regex patterns

- is useful for regex patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is useful for regex patterns")
val pattern = '\d+\.\d+'
expect pattern.contains("\\d") == true
```

</details>

#### triple-quoted strings (docstrings)

#### creates multi-line string

- creates multi-line string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multi-line string")
val s = """line1
```

</details>

#### preserves braces literally

- preserves braces literally


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves braces literally")
val s = """{name}"""
expect s == '{name}'  # Raw string for comparison
```

</details>

#### allows embedded double quotes

- allows embedded double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows embedded double quotes")
val s = """He said "hello" """
expect s.contains("\"") == true
```

</details>

#### raw double-quoted strings (r prefix)

#### creates raw string with double quotes

- creates raw string with double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates raw string with double quotes")
val s = r"hello"
expect s == "hello"
```

</details>

#### preserves backslashes

- preserves backslashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves backslashes")
val s = r"C:\Users\name"
expect s.contains("\\") == true
```

</details>

#### preserves braces

- preserves braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves braces")
val s = r"{name}"
expect s == '{name}'  # Raw string for comparison
```

</details>

#### is useful for Windows paths

- is useful for Windows paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is useful for Windows paths")
val path = r"C:\Program Files\App"
expect path.starts_with("C:") == true
```

</details>

#### raw triple-quoted strings (r prefix)

#### creates multi-line raw string

- creates multi-line raw string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multi-line raw string")
val s = r"""line1
```

</details>

#### preserves backslashes in multi-line

- preserves backslashes in multi-line


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves backslashes in multi-line")
val s = r"""path\to
```

</details>

#### explicit f-string prefix (redundant but valid)

#### works same as regular double-quoted

- works same as regular double-quoted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works same as regular double-quoted")
val name = "World"
val s = f"Hello, {name}!"
expect s == "Hello, World!"
```

</details>

#### supports expressions

- supports expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports expressions")
val s = f"Result: {2 * 3}"
expect s == "Result: 6"
```

</details>

#### triple-quoted f-strings (f prefix)

#### creates multi-line interpolated string

- creates multi-line interpolated string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multi-line interpolated string")
val name = "World"
val s = f"""Hello, {name}!
```

</details>

#### supports expressions in multi-line

- supports expressions in multi-line


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports expressions in multi-line")
val s = f"""Sum: {1 + 2}
```

</details>

#### allows embedded double quotes

- allows embedded double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows embedded double quotes")
val name = "test"
val s = f"""He said "{name}" """
expect s.contains("\"test\"") == true
```

</details>

#### escapes braces with double braces

- escapes braces with double braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes braces with double braces")
val value = 42
val json = f"""{{"key": {value}}}"""
expect json.contains('{') == true  # Use raw string to check for literal {
expect json.contains("42") == true
```

</details>

#### string type compatibility

#### all string types are compatible

- all string types are compatible


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all string types are compatible")
val a = "hello"
val b = 'hello'
val c = """hello"""
val d = r"hello"
expect a == b
expect b == c
expect c == d
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_literals_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text Literal Syntax.
- text Literal Syntax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `f39fd17f5599ed523b169f0c1b3d6d7de09fbb8973cdabcdd01bf6383e1411eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f39fd17f5599ed523b169f0c1b3d6d7de09fbb8973cdabcdd01bf6383e1411eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f39fd17f5599ed523b169f0c1b3d6d7de09fbb8973cdabcdd01bf6383e1411eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/string_literals_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_literals_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/string_literals_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_literals_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_literals_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates simple string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_literals_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports escape sequences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_literals_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports expression interpolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
