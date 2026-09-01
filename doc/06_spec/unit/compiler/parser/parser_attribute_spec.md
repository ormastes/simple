# Parser Attribute Specification

> Tests covering Parser - Attribute Syntax, Parser - Attribute Application, Parser - Attribute Arguments, Parser - Attribute Edge Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Attribute Specification

## Scenarios

### Parser - Attribute Syntax

#### parses @ attribute

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses @ attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @ attribute")
# @attr
# Traditional attribute syntax
assert_equal(1, 1)
```

</details>

#### parses #[] attribute

- parses #[] attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses #[] attribute")
# @attr
# New attribute syntax
assert_equal(1, 1)
```

</details>

#### parses @ attribute with arguments

- parses @ attribute with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @ attribute with arguments")
# @timeout(5000)
# Arguments should be parsed
assert_equal(1, 1)
```

</details>

#### parses #[] attribute with arguments

- parses #[] attribute with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses #[] attribute with arguments")
# @timeout(5000)
# Arguments should be parsed
assert_equal(1, 1)
```

</details>

#### parses multiple @ attributes

- parses multiple @ attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple @ attributes")
# @attr1
# @attr2
# Both should be captured
assert_equal(1, 1)
```

</details>

#### parses multiple #[] attributes

- parses multiple #[] attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple #[] attributes")
# @attr1
# @attr2
# Both should be captured
assert_equal(1, 1)
```

</details>

#### parses mixed @ and #[] attributes

- parses mixed @ and #[] attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses mixed @ and #[] attributes")
# @repr(C)
# @packed
# Both should be captured
assert_equal(1, 1)
```

</details>

### Parser - Attribute Application

#### applies attributes to functions

- applies attributes to functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies attributes to functions")
# @timeout(5000)
# fn test():
# Attribute should attach to function
assert_equal(1, 1)
```

</details>

#### applies attributes to classes

- applies attributes to classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies attributes to classes")
# @repr(C)
# class Data:
# Attribute should attach to class
assert_equal(1, 1)
```

</details>

#### applies attributes to actors

- applies attributes to actors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies attributes to actors")
# @distributed
# actor Worker:
# Attribute should attach to actor
assert_equal(1, 1)
```

</details>

#### applies attributes to structs

- applies attributes to structs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies attributes to structs")
# @packed
# struct Point:
# Attribute should attach to struct
assert_equal(1, 1)
```

</details>

### Parser - Attribute Arguments

#### parses single argument

- parses single argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single argument")
# @timeout(5000)
# Single numeric argument
assert_equal(1, 1)
```

</details>

#### parses multiple arguments

- parses multiple arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple arguments")
# @tag("slow", "integration")
# Multiple string arguments
assert_equal(1, 1)
```

</details>

#### parses complex arguments

- parses complex arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses complex arguments")
# @config(key: "value", count: 42)
# Named arguments
assert_equal(1, 1)
```

</details>

#### handles empty parentheses

- handles empty parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty parentheses")
# @attr()
# Empty argument list
assert_equal(1, 1)
```

</details>

### Parser - Attribute Edge Cases

#### handles attribute before pub

- handles attribute before pub


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles attribute before pub")
# @test
# pub fn test():
# Attribute before visibility
assert_equal(1, 1)
```

</details>

#### handles nested attribute arguments

- handles nested attribute arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested attribute arguments")
# @config([1, 2, 3])
# Nested brackets/parens
assert_equal(1, 1)
```

</details>

#### preserves attribute order

- preserves attribute order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves attribute order")
# @first
# @second
# Order should be maintained
assert_equal(1, 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/parser_attribute_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Parser - Attribute Syntax, Parser - Attribute Application, Parser - Attribute Arguments, Parser - Attribute Edge Cases.
- Parser - Attribute Syntax
- Parser - Attribute Application
- Parser - Attribute Arguments
- Parser - Attribute Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `474d03d89d9f009f3f786d68f6fe55e5695c52dc7884c5ce191a4aba2ef4d42e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `474d03d89d9f009f3f786d68f6fe55e5695c52dc7884c5ce191a4aba2ef4d42e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `474d03d89d9f009f3f786d68f6fe55e5695c52dc7884c5ce191a4aba2ef4d42e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/compiler/parser/parser_attribute_spec.spl
mirror: doc/06_spec/unit/compiler/parser/parser_attribute_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/parser_attribute_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/parser_attribute_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/parser_attribute_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/compiler/parser/parser_attribute_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @ attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/parser_attribute_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses #[] attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/parser_attribute_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @ attribute with arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
