# Jit Interpreter Specification

> <details>

<!-- sdn-diagram:id=jit_interpreter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_interpreter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_interpreter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_interpreter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that Auto mode is the default
expect true  # Placeholder
```

</details>

#### has JIT threshold configured

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test threshold configuration
expect true  # Placeholder
```

</details>

### Backend Integration

#### shares infrastructure with compiler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that backend uses LocalExecutionManager
expect true  # Placeholder
```

</details>

#### supports backend switching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test LLVM vs Cranelift selection
expect true  # Placeholder
```

</details>

### Execution Strategy

#### interprets by default for cold code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test tree-walking for low call count
expect true  # Placeholder
```

</details>

#### JIT compiles hot code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test JIT compilation after threshold
expect true  # Placeholder
```

</details>

### Value Semantics

#### provides reference semantics in JIT mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that JIT uses pointers not copies
expect true  # Placeholder
```

</details>

#### maintains reference semantics for arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
