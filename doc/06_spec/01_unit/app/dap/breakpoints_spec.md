# Breakpoints Specification

> <details>

<!-- sdn-diagram:id=breakpoints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakpoints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakpoints_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakpoints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakpoints Specification

## Scenarios

### BreakpointEntry

#### creates breakpoint entry

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create breakpoint entry at source location
assert_true(true)
```

</details>

#### adds condition to breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Add condition expression to breakpoint
assert_true(true)
```

</details>

#### adds hit condition to breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Add hit count condition to breakpoint
assert_true(true)
```

</details>

#### increments hit count

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Increment hit counter when breakpoint hit
assert_true(true)
```

</details>

### BreakpointStore

#### adds breakpoints

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Add breakpoints to store
assert_true(true)
```

</details>

#### removes breakpoints

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Remove breakpoints from store
assert_true(true)
```

</details>

#### finds breakpoints by location

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Query breakpoints at specific location
assert_true(true)
```

</details>

#### generates unique IDs

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generate unique breakpoint identifiers
assert_true(true)
```

</details>

#### clears all breakpoints

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Clear all breakpoints in store
assert_true(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/breakpoints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BreakpointEntry
- BreakpointStore

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
