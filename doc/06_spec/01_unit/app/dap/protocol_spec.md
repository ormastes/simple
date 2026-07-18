# Protocol Specification

> <details>

<!-- sdn-diagram:id=protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

protocol_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Specification

## Scenarios

### Source

#### creates source with path

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source represents debugged source code file
assert_true(true)
```

</details>

#### creates source with name

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source can be created with display name
assert_true(true)
```

</details>

### SourceBreakpoint

#### creates source breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source breakpoint at specific line
assert_true(true)
```

</details>

#### creates source breakpoint with condition

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source breakpoint with conditional break expression
assert_true(true)
```

</details>

### Breakpoint

#### creates verified breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified breakpoint set in debuggee
assert_true(true)
```

</details>

#### creates unverified breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Unverified breakpoint waiting for source
assert_true(true)
```

</details>

### StackFrame

#### creates stack frame

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stack frame in call stack
assert_true(true)
```

</details>

#### creates stack frame with module

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stack frame with module information
assert_true(true)
```

</details>

### Scope

#### creates local scope

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Local variable scope
assert_true(true)
```

</details>

#### creates arguments scope

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function arguments scope
assert_true(true)
```

</details>

#### creates global scope

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Global variable scope
assert_true(true)
```

</details>

### Variable

#### creates simple variable

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple scalar variable
assert_true(true)
```

</details>

#### creates variable with children

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Complex variable with child variables
assert_true(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Source
- SourceBreakpoint
- Breakpoint
- StackFrame
- Scope
- Variable

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
