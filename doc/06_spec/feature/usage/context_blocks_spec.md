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
| Source | `test/feature/usage/context_blocks_spec.spl` |
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
    # @req REQ-SSPEC-FEATURE
    step("executes code within context scope")
skip

context "Nested contexts":
it "supports properly nested context blocks":
    # @req REQ-SSPEC-FEATURE
    step("supports properly nested context blocks")
skip

context "Context variables":
it "maintains context-scoped variables":
    # @req REQ-SSPEC-FEATURE
    step("maintains context-scoped variables")
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

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("executes code within context scope")
skip
```

</details>

#### Setup and teardown

#### runs setup before and teardown after context

- runs setup before and teardown after context


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("runs setup before and teardown after context")
skip
```

</details>

#### Nested contexts

#### supports properly nested context blocks

- supports properly nested context blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports properly nested context blocks")
skip
```

</details>

#### Exception handling in contexts

#### ensures cleanup even when exceptions occur

- ensures cleanup even when exceptions occur


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ensures cleanup even when exceptions occur")
skip
```

</details>

#### Context variables

#### maintains context-scoped variables

- maintains context-scoped variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maintains context-scoped variables")
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f93c414540ba16c87d9c83e5fbc10444e8fabb72746ed0aade582a74e5482de2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f93c414540ba16c87d9c83e5fbc10444e8fabb72746ed0aade582a74e5482de2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f93c414540ba16c87d9c83e5fbc10444e8fabb72746ed0aade582a74e5482de2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/feature/usage/context_blocks_spec.spl
mirror: doc/06_spec/feature/usage/context_blocks_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/feature/usage/context_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/context_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/context_blocks_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/feature/usage/context_blocks_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes code within context scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/context_blocks_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs setup before and teardown after context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/context_blocks_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports properly nested context blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
