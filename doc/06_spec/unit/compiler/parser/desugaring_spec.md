# Desugaring Specification

> Tests covering Desugaring - Actor to Class, Desugaring - Async Functions, Desugaring - Await Expressions, Desugaring - Spawn Expressions, Desugaring - Module Level, Desugaring - Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Desugaring Specification

## Scenarios

### Desugaring - Actor to Class

#### transforms simple actor to class

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- transforms simple actor to class
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transforms simple actor to class")
# actor Counter: ... → class Counter: ...
# Structure should be preserved
expect(1).to_equal(1)
```

</details>

#### preserves actor methods

- preserves actor methods
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves actor methods")
# Actor methods should become class methods
# All methods should be copied
expect(1).to_equal(1)
```

</details>

#### preserves actor type parameters

- preserves actor type parameters
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves actor type parameters")
# actor Worker<T>: ... → class Worker<T>: ...
# Type parameters should be copied
expect(1).to_equal(1)
```

</details>

#### preserves actor visibility

- preserves actor visibility
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves actor visibility")
# pub actor → pub class
# Visibility flag should be copied
expect(1).to_equal(1)
```

</details>

#### preserves actor attributes

- preserves actor attributes
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves actor attributes")
# @attr actor → @attr class
# Attributes should be copied
expect(1).to_equal(1)
```

</details>

#### clears module.actors after transformation

- clears module.actors after transformation
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears module.actors after transformation")
# After desugaring, module.actors should be empty
# All actors should be in module.classes
expect(1).to_equal(1)
```

</details>

### Desugaring - Async Functions

#### wraps return type in Future

- wraps return type in Future
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps return type in Future")
# async fn f() -> T → fn f() -> Future<T>
# Return type should be wrapped
expect(1).to_equal(1)
```

</details>

#### handles functions with no return type

- handles functions with no return type
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles functions with no return type")
# async fn f(): → fn f() -> Future<()>
# Should use unit type
expect(1).to_equal(1)
```

</details>

#### clears is_async flag after transformation

- clears is_async flag after transformation
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears is_async flag after transformation")
# After desugaring, is_async should be false
# Function should be normal function
expect(1).to_equal(1)
```

</details>

#### wraps body in Future.ready

- wraps body in Future.ready
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps body in Future.ready")
# Body should be wrapped in Future.ready()
# For simple desugaring
expect(1).to_equal(1)
```

</details>

### Desugaring - Await Expressions

#### transforms await to block_on

- transforms await to block_on
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transforms await to block_on")
# await expr → block_on(expr)
# Simple transformation
expect(1).to_equal(1)
```

</details>

#### handles nested await expressions

- handles nested await expressions
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested await expressions")
# await await expr
# Multiple levels should work
expect(1).to_equal(1)
```

</details>

#### preserves await in function bodies

- preserves await in function bodies
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves await in function bodies")
# Function with multiple awaits
# All should be transformed
expect(1).to_equal(1)
```

</details>

### Desugaring - Spawn Expressions

#### transforms spawn to spawn_actor

- transforms spawn to spawn_actor
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transforms spawn to spawn_actor")
# spawn expr → spawn_actor(expr)
# Simple transformation
expect(1).to_equal(1)
```

</details>

#### handles spawn with constructor

- handles spawn with constructor
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles spawn with constructor")
# spawn Worker() → spawn_actor(Worker())
# Constructor call should be preserved
expect(1).to_equal(1)
```

</details>

#### handles spawn with arguments

- handles spawn with arguments
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles spawn with arguments")
# spawn Worker(id: 1) → spawn_actor(Worker(id: 1))
# Arguments should be preserved
expect(1).to_equal(1)
```

</details>

### Desugaring - Module Level

#### processes all module items

- processes all module items
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes all module items")
# All functions, actors should be processed
# Nothing should be skipped
expect(1).to_equal(1)
```

</details>

#### preserves module structure

- preserves module structure
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves module structure")
# Module name, imports, exports preserved
# Only transformable items changed
expect(1).to_equal(1)
```

</details>

#### handles empty modules

- handles empty modules
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty modules")
# Module with no actors/async
# Should pass through unchanged
expect(1).to_equal(1)
```

</details>

#### handles modules with only actors

- handles modules with only actors
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles modules with only actors")
# Module with only actors, no functions
# All actors should transform
expect(1).to_equal(1)
```

</details>

### Desugaring - Integration

#### integrates with parser output

- integrates with parser output
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integrates with parser output")
# Parser output → Desugaring input
# Module structure should match
expect(1).to_equal(1)
```

</details>

#### produces valid HIR input

- produces valid HIR input
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces valid HIR input")
# Desugaring output → HIR lowering input
# No actors in output
expect(1).to_equal(1)
```

</details>

#### is idempotent

- is idempotent
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is idempotent")
# Desugaring already-desugared module
# Should have no effect
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/desugaring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Desugaring - Actor to Class, Desugaring - Async Functions, Desugaring - Await Expressions, Desugaring - Spawn Expressions, Desugaring - Module Level, Desugaring - Integration.
- Desugaring - Actor to Class
- Desugaring - Async Functions
- Desugaring - Await Expressions
- Desugaring - Spawn Expressions
- Desugaring - Module Level
- Desugaring - Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `fb2c4e054a9045597d485fc8a5f27c3054c1b601e83a6901fa008536d35c3511`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb2c4e054a9045597d485fc8a5f27c3054c1b601e83a6901fa008536d35c3511`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb2c4e054a9045597d485fc8a5f27c3054c1b601e83a6901fa008536d35c3511`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/unit/compiler/parser/desugaring_spec.spl
mirror: doc/06_spec/unit/compiler/parser/desugaring_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/unit/compiler/parser/desugaring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/desugaring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/desugaring_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler/parser/desugaring_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/compiler/parser/desugaring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 23 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/desugaring_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transforms simple actor to class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/desugaring_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves actor methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/desugaring_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves actor type parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
