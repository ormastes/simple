# Scoped Context Blocks for Resource Management

> Context blocks provide scoped execution environments that guarantee setup and teardown semantics, similar to Python's `with` statement or RAII in C++. They enable safe resource management by ensuring cleanup code runs regardless of how the block exits. This spec validates basic context execution, nested context support, variable scoping within contexts, and proper cleanup guarantees when exceptions occur.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scoped Context Blocks for Resource Management

Context blocks provide scoped execution environments that guarantee setup and teardown semantics, similar to Python's `with` statement or RAII in C++. They enable safe resource management by ensuring cleanup code runs regardless of how the block exits. This spec validates basic context execution, nested context support, variable scoping within contexts, and proper cleanup guarantees when exceptions occur.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-040 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/context_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Context blocks provide scoped execution environments that guarantee setup and teardown
semantics, similar to Python's `with` statement or RAII in C++. They enable safe resource
management by ensuring cleanup code runs regardless of how the block exits. This spec
validates basic context execution, nested context support, variable scoping within
contexts, and proper cleanup guarantees when exceptions occur.

## Syntax

```simple
context "Basic context execution":
it "executes code within context scope":
    # @req REQ-SSPEC-SYSTEM
    step("executes code within context scope")
    # evidence(protocol_json): asserted result fields below are the complete typed oracle
skip

context "Nested contexts":
it "supports properly nested context blocks":
    # @req REQ-SSPEC-SYSTEM
    step("supports properly nested context blocks")
    # evidence(protocol_json): asserted result fields below are the complete typed oracle
skip

context "Context variables":
it "maintains context-scoped variables":
    # @req REQ-SSPEC-SYSTEM
    step("maintains context-scoped variables")
    # evidence(protocol_json): asserted result fields below are the complete typed oracle
skip
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Context block | A scoped execution region with guaranteed setup/teardown |
| Setup/teardown | Code that runs before and after the context body executes |
| Nested contexts | Contexts within contexts, with proper ordering of cleanup |
| Context variables | Variables whose lifetime is bound to the enclosing context scope |

## Scenarios

### Context Blocks

#### Basic context execution

#### executes code within context scope

- executes code within context scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes code within context scope")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
skip
```

</details>

#### Setup and teardown

#### runs setup before and teardown after context

- runs setup before and teardown after context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs setup before and teardown after context")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
skip
```

</details>

#### Nested contexts

#### supports properly nested context blocks

- supports properly nested context blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports properly nested context blocks")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
skip
```

</details>

#### Exception handling in contexts

#### ensures cleanup even when exceptions occur

- ensures cleanup even when exceptions occur


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ensures cleanup even when exceptions occur")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
skip
```

</details>

#### Context variables

#### maintains context-scoped variables

- maintains context-scoped variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains context-scoped variables")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
skip
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7eecbb273687b4331dd1bf3f3577249229aa16ba85be375c4aa43273feaaf7a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7eecbb273687b4331dd1bf3f3577249229aa16ba85be375c4aa43273feaaf7a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7eecbb273687b4331dd1bf3f3577249229aa16ba85be375c4aa43273feaaf7a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/usage/context_blocks_spec.spl
mirror: doc/06_spec/03_system/feature/usage/context_blocks_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/feature/usage/context_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/context_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/context_blocks_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->
