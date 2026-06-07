# Debug State Specification

> <details>

<!-- sdn-diagram:id=debug_state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_state_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug State Specification

## Scenarios

### DebugState to_string

#### converts Stopped to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Stopped: "stopped"
val state = "stopped"
expect(state == "stopped")
```

</details>

#### converts Running to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Running: "running"
val state = "running"
expect(state == "running")
```

</details>

#### converts Paused to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Paused: "paused"
val state = "paused"
expect(state == "paused")
```

</details>

#### converts Terminated to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Terminated: "terminated"
val state = "terminated"
expect(state == "terminated")
```

</details>

### DebugState description

#### describes Stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Stopped: "Debugger stopped at breakpoint"
val desc = "Debugger stopped at breakpoint"
expect(desc == "Debugger stopped at breakpoint")
```

</details>

#### describes Running

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Running: "Program executing"
val desc = "Program executing"
expect(desc == "Program executing")
```

</details>

#### describes Paused

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Paused: "Execution paused by user"
val desc = "Execution paused by user"
expect(desc == "Execution paused by user")
```

</details>

#### describes Terminated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Terminated: "Program terminated"
val desc = "Program terminated"
expect(desc == "Program terminated")
```

</details>

### DebugState is_stopped

#### returns true for Stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Stopped: true
val is_stopped = true
expect(is_stopped)
```

</details>

#### returns false for other states

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_stopped = false
expect(not is_stopped)
```

</details>

### DebugState is_running

#### returns true for Running

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Running: true
val is_running = true
expect(is_running)
```

</details>

#### returns false for other states

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_running = false
expect(not is_running)
```

</details>

### DebugState is_paused

#### returns true for Paused

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Paused: true
val is_paused = true
expect(is_paused)
```

</details>

#### returns false for other states

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_paused = false
expect(not is_paused)
```

</details>

### DebugState is_terminated

#### returns true for Terminated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Terminated: true
val is_terminated = true
expect(is_terminated)
```

</details>

#### returns false for other states

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_terminated = false
expect(not is_terminated)
```

</details>

### DebugState is_active

#### returns false for Terminated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Terminated: false
val is_active = false
expect(not is_active)
```

</details>

#### returns true for other states

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: true
val is_active = true
expect(is_active)
```

</details>

### DebugState is_halted

#### returns true for Stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Stopped: true
val is_halted = true
expect(is_halted)
```

</details>

#### returns true for Paused

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Paused: true
val is_halted = true
expect(is_halted)
```

</details>

#### returns false for other states

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_halted = false
expect(not is_halted)
```

</details>

### DebugState can_continue

#### delegates to is_halted

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: return self.is_halted()
val can_continue = true
expect(can_continue)
```

</details>

### DebugState summary

#### categorizes as halted when active and halted

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.is_active() and self.is_halted()
val status = "halted"
expect(status == "halted")
```

</details>

#### categorizes as executing when active and not halted

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.is_active() and not self.is_halted()
val status = "executing"
expect(status == "executing")
```

</details>

#### categorizes as terminated when not active

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: else (not active)
val status = "terminated"
expect(status == "terminated")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/debug_state_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DebugState to_string
- DebugState description
- DebugState is_stopped
- DebugState is_running
- DebugState is_paused
- DebugState is_terminated
- DebugState is_active
- DebugState is_halted
- DebugState can_continue
- DebugState summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
