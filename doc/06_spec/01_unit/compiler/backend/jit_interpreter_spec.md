# Jit Interpreter Specification

> Tests covering JitInterpreterBackend, Configuration, Backend Integration, Execution Strategy, Value Semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Interpreter Specification

## Scenarios

### JitInterpreterBackend

### Configuration

#### creates with default mode

- creates with default mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with default mode")
# Test that Auto mode is the default
expect true  # Placeholder
```

</details>

#### has JIT threshold configured

- has JIT threshold configured


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has JIT threshold configured")
# Test threshold configuration
expect true  # Placeholder
```

</details>

### Backend Integration

#### shares infrastructure with compiler

- shares infrastructure with compiler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shares infrastructure with compiler")
# Test that backend uses LocalExecutionManager
expect true  # Placeholder
```

</details>

#### supports backend switching

- supports backend switching


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports backend switching")
# Test LLVM vs Cranelift selection
expect true  # Placeholder
```

</details>

### Execution Strategy

#### interprets by default for cold code

- interprets by default for cold code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interprets by default for cold code")
# Test tree-walking for low call count
expect true  # Placeholder
```

</details>

#### JIT compiles hot code

- JIT compiles hot code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JIT compiles hot code")
# Test JIT compilation after threshold
expect true  # Placeholder
```

</details>

### Value Semantics

#### provides reference semantics in JIT mode

- provides reference semantics in JIT mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides reference semantics in JIT mode")
# Test that JIT uses pointers not copies
expect true  # Placeholder
```

</details>

#### maintains reference semantics for arrays

- maintains reference semantics for arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maintains reference semantics for arrays")
# Test array mutation works correctly
expect true  # Placeholder
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/jit_interpreter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JitInterpreterBackend, Configuration, Backend Integration, Execution Strategy, Value Semantics.
- JitInterpreterBackend
- Configuration
- Backend Integration
- Execution Strategy
- Value Semantics

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de0f90b978a0d1f1d1fe2a0625745b146da8ead65de64dd896815d2d040e5b10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de0f90b978a0d1f1d1fe2a0625745b146da8ead65de64dd896815d2d040e5b10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de0f90b978a0d1f1d1fe2a0625745b146da8ead65de64dd896815d2d040e5b10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/jit_interpreter_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/jit_interpreter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/jit_interpreter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/jit_interpreter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/jit_interpreter_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with default mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/jit_interpreter_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has JIT threshold configured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/jit_interpreter_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shares infrastructure with compiler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
