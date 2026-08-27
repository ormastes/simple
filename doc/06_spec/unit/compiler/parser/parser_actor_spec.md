# Parser Actor Specification

> Tests covering Parser - Actor Definitions, Parser - Actor Methods, Parser - Actor Structure, Parser - Actor Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Actor Specification

## Scenarios

### Parser - Actor Definitions

#### parses simple actor definition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses simple actor definition
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple actor definition")
# Simple actor with one method
# Should parse without errors
expect(1).to_equal(1)
```

</details>

#### parses actor with multiple methods

- parses actor with multiple methods
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses actor with multiple methods")
# Actor with several methods
# All methods should be recognized
expect(1).to_equal(1)
```

</details>

#### parses actor with type parameters

- parses actor with type parameters
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses actor with type parameters")
# actor Worker<T>:
# Type parameters should be parsed
expect(1).to_equal(1)
```

</details>

#### parses public actor

- parses public actor
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses public actor")
# pub actor Counter:
# Visibility flag should be set
expect(1).to_equal(1)
```

</details>

#### parses actor with doc comment

- parses actor with doc comment
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses actor with doc comment")
# Actor with documentation
# Doc comment should be captured
expect(1).to_equal(1)
```

</details>

### Parser - Actor Methods

#### parses immutable methods

- parses immutable methods
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses immutable methods")
# fn method():
# Should parse as immutable method
expect(1).to_equal(1)
```

</details>

#### parses mutable methods

- parses mutable methods
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses mutable methods")
# me method():
# Should parse as mutable method
expect(1).to_equal(1)
```

</details>

#### parses static methods

- parses static methods
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses static methods")
# static fn factory():
# Should parse as static method
expect(1).to_equal(1)
```

</details>

#### parses methods with parameters

- parses methods with parameters
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses methods with parameters")
# fn process(task: Task):
# Parameters should be parsed
expect(1).to_equal(1)
```

</details>

#### parses methods with return types

- parses methods with return types
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses methods with return types")
# fn get_value() -> i64:
# Return type should be parsed
expect(1).to_equal(1)
```

</details>

### Parser - Actor Structure

#### handles multiple actors in one file

- handles multiple actors in one file
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple actors in one file")
# Multiple actor definitions
# All should be parsed correctly
expect(1).to_equal(1)
```

</details>

#### distinguishes actors from classes

- distinguishes actors from classes
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes actors from classes")
# Both actor and class in same file
# Should populate different dicts
expect(1).to_equal(1)
```

</details>

#### parses empty actor

- parses empty actor
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty actor")
# actor Empty:
#     pass
# Should create valid actor
expect(1).to_equal(1)
```

</details>

### Parser - Actor Integration

#### integrates with outline parser

- integrates with outline parser
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integrates with outline parser")
# Outline parser should recognize actor
# Should create ActorOutline
expect(1).to_equal(1)
```

</details>

#### integrates with full parser

- integrates with full parser
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integrates with full parser")
# Full parser should convert ActorOutline -> Actor
# Should populate module.actors
expect(1).to_equal(1)
```

</details>

#### works with desugaring

- works with desugaring
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with desugaring")
# Desugaring should convert actor -> class
# module.actors should be cleared
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/parser_actor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Parser - Actor Definitions, Parser - Actor Methods, Parser - Actor Structure, Parser - Actor Integration.
- Parser - Actor Definitions
- Parser - Actor Methods
- Parser - Actor Structure
- Parser - Actor Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `bc4d97002f9c7a70c343c06edaa65eaaae0841ea35407fd52b52fb9a9b8db180`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc4d97002f9c7a70c343c06edaa65eaaae0841ea35407fd52b52fb9a9b8db180`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc4d97002f9c7a70c343c06edaa65eaaae0841ea35407fd52b52fb9a9b8db180`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/unit/compiler/parser/parser_actor_spec.spl
mirror: doc/06_spec/unit/compiler/parser/parser_actor_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/unit/compiler/parser/parser_actor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/parser_actor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/parser_actor_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler/parser/parser_actor_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/compiler/parser/parser_actor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/parser_actor_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple actor definition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/parser_actor_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses actor with multiple methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/parser_actor_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses actor with type parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
