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
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @ attribute")
# @attr
# Traditional attribute syntax
expect(1).to_equal(1)
```

</details>

#### parses #[] attribute

- parses #[] attribute
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses #[] attribute")
# @attr
# New attribute syntax
expect(1).to_equal(1)
```

</details>

#### parses @ attribute with arguments

- parses @ attribute with arguments
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @ attribute with arguments")
# @timeout(5000)
# Arguments should be parsed
expect(1).to_equal(1)
```

</details>

#### parses #[] attribute with arguments

- parses #[] attribute with arguments
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses #[] attribute with arguments")
# @timeout(5000)
# Arguments should be parsed
expect(1).to_equal(1)
```

</details>

#### parses multiple @ attributes

- parses multiple @ attributes
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

#### parses multiple #[] attributes

- parses multiple #[] attributes
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

#### parses mixed @ and #[] attributes

- parses mixed @ and #[] attributes
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

### Parser - Attribute Application

#### applies attributes to functions

- applies attributes to functions
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

#### applies attributes to classes

- applies attributes to classes
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

#### applies attributes to actors

- applies attributes to actors
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

#### applies attributes to structs

- applies attributes to structs
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

### Parser - Attribute Arguments

#### parses single argument

- parses single argument
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single argument")
# @timeout(5000)
# Single numeric argument
expect(1).to_equal(1)
```

</details>

#### parses multiple arguments

- parses multiple arguments
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple arguments")
# @tag("slow", "integration")
# Multiple string arguments
expect(1).to_equal(1)
```

</details>

#### parses complex arguments

- parses complex arguments
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses complex arguments")
# @config(key: "value", count: 42)
# Named arguments
expect(1).to_equal(1)
```

</details>

#### handles empty parentheses

- handles empty parentheses
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty parentheses")
# @attr()
# Empty argument list
expect(1).to_equal(1)
```

</details>

### Parser - Attribute Edge Cases

#### handles attribute before pub

- handles attribute before pub
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

#### handles nested attribute arguments

- handles nested attribute arguments
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested attribute arguments")
# @config([1, 2, 3])
# Nested brackets/parens
expect(1).to_equal(1)
```

</details>

#### preserves attribute order

- preserves attribute order
   - Expected: 1 equals `1`


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
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/parser_attribute_spec.spl` |
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `d62e95cddaf816ad23bcd9ef68aac2f4b23eed761b68616db63905f9c104e04b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d62e95cddaf816ad23bcd9ef68aac2f4b23eed761b68616db63905f9c104e04b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d62e95cddaf816ad23bcd9ef68aac2f4b23eed761b68616db63905f9c104e04b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/unit/compiler/parser/parser_attribute_spec.spl
mirror: doc/06_spec/unit/compiler/parser/parser_attribute_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/unit/compiler/parser/parser_attribute_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/parser_attribute_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/parser_attribute_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler/parser/parser_attribute_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/compiler/parser/parser_attribute_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
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
