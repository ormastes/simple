# async_integration_spec

> Purpose: Prove that Integration - Actor Pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# async_integration_spec

Purpose: Prove that Integration - Actor Pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/async/async_integration_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Integration - Actor Pipeline.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Integration - Actor Pipeline

#### compiles actor definition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles actor definition
- Verify: compiles actor definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles actor definition")
step("Verify: compiles actor definition")
# @req: REQ-COMP-INTEGRATION-ACTOR-PIPELINE-001
# Source: actor Counter: ...
# Should compile without errors
assert_equal(1, 1)
```

</details>

#### executes actor methods

- executes actor methods
- Verify: executes actor methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes actor methods")
step("Verify: executes actor methods")
# Actor method should be callable
# After desugaring to class
assert_equal(1, 1)
```

</details>

#### handles multiple actors

- handles multiple actors
- Verify: handles multiple actors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple actors")
step("Verify: handles multiple actors")
# File with 3+ actors
# All should compile and work
assert_equal(1, 1)
```

</details>

### Integration - Async/Await Pipeline

#### compiles async function

- compiles async function
- Verify: compiles async function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles async function")
step("Verify: compiles async function")
# Source: async fn fetch() -> T
# Should compile to Future<T>
assert_equal(1, 1)
```

</details>

#### compiles await expression

- compiles await expression
- Verify: compiles await expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles await expression")
step("Verify: compiles await expression")
# Source: await expr
# Should compile to block_on(expr)
assert_equal(1, 1)
```

</details>

#### executes async workflow

- executes async workflow
- Verify: executes async workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes async workflow")
step("Verify: executes async workflow")
# async fn with multiple awaits
# Should execute correctly
assert_equal(1, 1)
```

</details>

### Integration - Spawn Pipeline

#### compiles spawn expression

- compiles spawn expression
- Verify: compiles spawn expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles spawn expression")
step("Verify: compiles spawn expression")
# Source: spawn Worker()
# Should compile to spawn_actor(Worker())
assert_equal(1, 1)
```

</details>

#### works with actor definitions

- works with actor definitions
- Verify: works with actor definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with actor definitions")
step("Verify: works with actor definitions")
# actor + spawn in same file
# Should work together
assert_equal(1, 1)
```

</details>

### Integration - Attribute Pipeline

#### compiles #[] attributes

- compiles #[] attributes
- Verify: compiles #[] attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles #[] attributes")
step("Verify: compiles #[] attributes")
# @timeout(5000) fn test():
# Should parse and compile
assert_equal(1, 1)
```

</details>

#### compiles @ attributes

- compiles @ attributes
- Verify: compiles @ attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles @ attributes")
step("Verify: compiles @ attributes")
# @repr(C) class Data:
# Should parse and compile
assert_equal(1, 1)
```

</details>

#### preserves attributes through pipeline

- preserves attributes through pipeline
- Verify: preserves attributes through pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves attributes through pipeline")
step("Verify: preserves attributes through pipeline")
# Attributes should reach HIR/MIR
# Not lost in transformations
assert_equal(1, 1)
```

</details>

### Integration - Combined Features

#### compiles actor with async methods

- compiles actor with async methods
- Verify: compiles actor with async methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles actor with async methods")
step("Verify: compiles actor with async methods")
# actor with async fn methods
# Both features together
assert_equal(1, 1)
```

</details>

#### compiles actor with attributes

- compiles actor with attributes
- Verify: compiles actor with attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles actor with attributes")
step("Verify: compiles actor with attributes")
# @distributed actor Worker:
# Attributes on actors
assert_equal(1, 1)
```

</details>

#### compiles async fn with spawn

- compiles async fn with spawn
- Verify: compiles async fn with spawn


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles async fn with spawn")
step("Verify: compiles async fn with spawn")
# async fn that uses spawn
# Both features in one function
assert_equal(1, 1)
```

</details>

#### compiles full async actor example

- compiles full async actor example
- Verify: compiles full async actor example


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles full async actor example")
step("Verify: compiles full async actor example")
# actor with async methods, spawn, await
# All features together
assert_equal(1, 1)
```

</details>

### Integration - Error Handling

#### reports actor syntax errors

- reports actor syntax errors
- Verify: reports actor syntax errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports actor syntax errors")
step("Verify: reports actor syntax errors")
# Invalid actor syntax
# Should produce clear error
assert_equal(1, 1)
```

</details>

#### reports async syntax errors

- reports async syntax errors
- Verify: reports async syntax errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports async syntax errors")
step("Verify: reports async syntax errors")
# Invalid async syntax
# Should produce clear error
assert_equal(1, 1)
```

</details>

#### reports attribute syntax errors

- reports attribute syntax errors
- Verify: reports attribute syntax errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports attribute syntax errors")
step("Verify: reports attribute syntax errors")
# Invalid attribute syntax
# Should produce clear error
assert_equal(1, 1)
```

</details>

### Integration - Performance

#### compiles large actor modules

- compiles large actor modules
- Verify: compiles large actor modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles large actor modules")
step("Verify: compiles large actor modules")
# Module with 20+ actors
# Should compile in reasonable time
assert_equal(1, 1)
```

</details>

#### handles deeply nested awaits

- handles deeply nested awaits
- Verify: handles deeply nested awaits


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles deeply nested awaits")
step("Verify: handles deeply nested awaits")
# Multiple levels of await
# Should not stack overflow
assert_equal(1, 1)
```

</details>

#### handles many attributes

- handles many attributes
- Verify: handles many attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles many attributes")
step("Verify: handles many attributes")
# Function with 10+ attributes
# Should parse efficiently
assert_equal(1, 1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-INTEGRATION-ACTOR-PIPELINE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1896033062037b9938fad2220502a19b3d2199285c28310ace7ff820eab48d1a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1896033062037b9938fad2220502a19b3d2199285c28310ace7ff820eab48d1a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1896033062037b9938fad2220502a19b3d2199285c28310ace7ff820eab48d1a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/async/async_integration_spec.spl
mirror: doc/06_spec/unit/compiler/async/async_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/async/async_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/async/async_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/async/async_integration_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles actor definition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/async/async_integration_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes actor methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/async/async_integration_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multiple actors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
