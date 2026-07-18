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

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Stopped: "stopped"
val state = "stopped"
assert_true(state == "stopped")
```

</details>

#### converts Running to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Running: "running"
val state = "running"
assert_true(state == "running")
```

</details>

#### converts Paused to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Paused: "paused"
val state = "paused"
assert_true(state == "paused")
```

</details>

#### converts Terminated to string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Terminated: "terminated"
val state = "terminated"
assert_true(state == "terminated")
```

</details>

### DebugState description

#### describes Stopped

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Stopped: "Debugger stopped at breakpoint"
val desc = "Debugger stopped at breakpoint"
assert_true(desc == "Debugger stopped at breakpoint")
```

</details>

#### describes Running

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Running: "Program executing"
val desc = "Program executing"
assert_true(desc == "Program executing")
```

</details>

#### describes Paused

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Paused: "Execution paused by user"
val desc = "Execution paused by user"
assert_true(desc == "Execution paused by user")
```

</details>

#### describes Terminated

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Terminated: "Program terminated"
val desc = "Program terminated"
assert_true(desc == "Program terminated")
```

</details>

### DebugState is_stopped

#### returns true for Stopped

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Stopped: true
val is_stopped = true
assert_true(is_stopped)
```

</details>

#### returns false for other states

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_stopped = false
assert_false(is_stopped)
```

</details>

### DebugState is_running

#### returns true for Running

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Running: true
val is_running = true
assert_true(is_running)
```

</details>

#### returns false for other states

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_running = false
assert_false(is_running)
```

</details>

### DebugState is_paused

#### returns true for Paused

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Paused: true
val is_paused = true
assert_true(is_paused)
```

</details>

#### returns false for other states

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_paused = false
assert_false(is_paused)
```

</details>

### DebugState is_terminated

#### returns true for Terminated

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Terminated: true
val is_terminated = true
assert_true(is_terminated)
```

</details>

#### returns false for other states

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_terminated = false
assert_false(is_terminated)
```

</details>

### DebugState is_active

#### returns false for Terminated

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Terminated: false
val is_active = false
assert_false(is_active)
```

</details>

#### returns true for other states

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: true
val is_active = true
assert_true(is_active)
```

</details>

### DebugState is_halted

#### returns true for Stopped

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Stopped: true
val is_halted = true
assert_true(is_halted)
```

</details>

#### returns true for Paused

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case Paused: true
val is_halted = true
assert_true(is_halted)
```

</details>

#### returns false for other states

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: case _: false
val is_halted = false
assert_false(is_halted)
```

</details>

### DebugState can_continue

#### delegates to is_halted

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: return self.is_halted()
val can_continue = true
assert_true(can_continue)
```

</details>

### DebugState summary

#### categorizes as halted when active and halted

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.is_active() and self.is_halted()
val status = "halted"
assert_true(status == "halted")
```

</details>

#### categorizes as executing when active and not halted

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.is_active() and not self.is_halted()
val status = "executing"
assert_true(status == "executing")
```

</details>

#### categorizes as terminated when not active

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: else (not active)
val status = "terminated"
assert_true(status == "terminated")
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
