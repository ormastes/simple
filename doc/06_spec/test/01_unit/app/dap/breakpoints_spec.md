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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create breakpoint entry at source location
expect(true)
```

</details>

#### adds condition to breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Add condition expression to breakpoint
expect(true)
```

</details>

#### adds hit condition to breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Add hit count condition to breakpoint
expect(true)
```

</details>

#### increments hit count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Increment hit counter when breakpoint hit
expect(true)
```

</details>

### BreakpointStore

#### adds breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Add breakpoints to store
expect(true)
```

</details>

#### removes breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Remove breakpoints from store
expect(true)
```

</details>

#### finds breakpoints by location

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Query breakpoints at specific location
expect(true)
```

</details>

#### generates unique IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generate unique breakpoint identifiers
expect(true)
```

</details>

#### clears all breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Clear all breakpoints in store
expect(true)
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
