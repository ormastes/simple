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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source represents debugged source code file
expect(true)
```

</details>

#### creates source with name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source can be created with display name
expect(true)
```

</details>

### SourceBreakpoint

#### creates source breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source breakpoint at specific line
expect(true)
```

</details>

#### creates source breakpoint with condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source breakpoint with conditional break expression
expect(true)
```

</details>

### Breakpoint

#### creates verified breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified breakpoint set in debuggee
expect(true)
```

</details>

#### creates unverified breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Unverified breakpoint waiting for source
expect(true)
```

</details>

### StackFrame

#### creates stack frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stack frame in call stack
expect(true)
```

</details>

#### creates stack frame with module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stack frame with module information
expect(true)
```

</details>

### Scope

#### creates local scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Local variable scope
expect(true)
```

</details>

#### creates arguments scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function arguments scope
expect(true)
```

</details>

#### creates global scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Global variable scope
expect(true)
```

</details>

### Variable

#### creates simple variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple scalar variable
expect(true)
```

</details>

#### creates variable with children

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Complex variable with child variables
expect(true)
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
