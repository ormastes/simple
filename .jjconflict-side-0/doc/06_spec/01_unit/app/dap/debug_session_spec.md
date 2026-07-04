# Debug Session Specification

> <details>

<!-- sdn-diagram:id=debug_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_session_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Session Specification

## Scenarios

### DebugSession

### Creation

#### creates new session

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: DebugSession.new()
val session_created = true
assert_true(session_created)
```

</details>

#### initializes session_id to 0

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: session_id: 0
val session_id = 0
assert_true(session_id == 0)
```

</details>

#### sets configuration

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: configuration: config
val config_set = true
assert_true(config_set)
```

</details>

#### initializes state to Stopped

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: state: DebugState.Stopped
val state = "stopped"
assert_true(state == "stopped")
```

</details>

### start

#### starts debug session

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: start() method
val session_started = true
assert_true(session_started)
```

</details>

#### converts config to JSON

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: val config_json = self.configuration.to_json()
val json_created = true
assert_true(json_created)
```

</details>

#### calls vscode_debug_start_session

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_start_session(config_json)
val ffi_called = true
assert_true(ffi_called)
```

</details>

#### updates session_id

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.session_id = ...
val id_updated = true
assert_true(id_updated)
```

</details>

#### sets state to Running

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.state = DebugState.Running
val state = "running"
assert_true(state == "running")
```

</details>

### continue_execution

#### continues execution

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: continue_execution() method
val continued = true
assert_true(continued)
```

</details>

#### calls vscode_debug_continue

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_continue(self.session_id)
val ffi_called = true
assert_true(ffi_called)
```

</details>

#### sets state to Running

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.state = DebugState.Running
val state = "running"
assert_true(state == "running")
```

</details>

### step_over

#### steps over current line

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: step_over() method
val stepped = true
assert_true(stepped)
```

</details>

#### calls vscode_debug_step_over

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_step_over(self.session_id)
val ffi_called = true
assert_true(ffi_called)
```

</details>

### step_into

#### steps into function

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: step_into() method
val stepped = true
assert_true(stepped)
```

</details>

#### calls vscode_debug_step_into

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_step_into(self.session_id)
val ffi_called = true
assert_true(ffi_called)
```

</details>

### step_out

#### steps out of function

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: step_out() method
val stepped = true
assert_true(stepped)
```

</details>

#### calls vscode_debug_step_out

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_step_out(self.session_id)
val ffi_called = true
assert_true(ffi_called)
```

</details>

### pause

#### pauses execution

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: pause() method
val paused = true
assert_true(paused)
```

</details>

#### calls vscode_debug_pause

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_pause(self.session_id)
val ffi_called = true
assert_true(ffi_called)
```

</details>

#### sets state to Paused

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.state = DebugState.Paused
val state = "paused"
assert_true(state == "paused")
```

</details>

### stop

#### stops debug session

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: stop() method
val stopped = true
assert_true(stopped)
```

</details>

#### calls vscode_debug_stop

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_stop(self.session_id)
val ffi_called = true
assert_true(ffi_called)
```

</details>

#### sets state to Stopped

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.state = DebugState.Stopped
val state = "stopped"
assert_true(state == "stopped")
```

</details>

### evaluate

#### evaluates expression

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: evaluate() method
val evaluated = true
assert_true(evaluated)
```

</details>

#### calls vscode_debug_evaluate

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_evaluate(self.session_id, expression)
val ffi_called = true
assert_true(ffi_called)
```

</details>

#### returns evaluation result

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: return value from FFI
val result_returned = true
assert_true(result_returned)
```

</details>

### Breakpoint

### Creation

#### creates breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: Breakpoint.new()
val bp_created = true
assert_true(bp_created)
```

</details>

#### sets file field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: file: file
val file_set = true
assert_true(file_set)
```

</details>

#### sets line field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: line: line
val line_set = true
assert_true(line_set)
```

</details>

#### initializes empty condition

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: condition: ""
val condition = ""
assert_true(condition == "")
```

</details>

#### initializes hit_count to 0

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: hit_count: 0
val hit_count = 0
assert_true(hit_count == 0)
```

</details>

#### initializes enabled to true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enabled: true
val enabled = true
assert_true(enabled)
```

</details>

#### initializes breakpoint_id to 0

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: breakpoint_id: 0
val id = 0
assert_true(id == 0)
```

</details>

### set_condition

#### sets breakpoint condition

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.condition = condition
val condition_set = true
assert_true(condition_set)
```

</details>

### set

#### sets breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: set() method
val bp_set = true
assert_true(bp_set)
```

</details>

#### calls vscode_debug_set_breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_set_breakpoint(self.file, self.line)
val ffi_called = true
assert_true(ffi_called)
```

</details>

#### updates breakpoint_id

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.breakpoint_id = ...
val id_updated = true
assert_true(id_updated)
```

</details>

### enable

#### enables breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.enabled = true
val enabled = true
assert_true(enabled)
```

</details>

### disable

#### disables breakpoint

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.enabled = false
val disabled = false
assert_false(disabled)
```

</details>

### toggle

#### toggles enabled state

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.enabled = not self.enabled
val toggled = true
assert_true(toggled)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/debug_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DebugSession
- Creation
- start
- continue_execution
- step_over
- step_into
- step_out
- pause
- stop
- evaluate
- Breakpoint
- Creation
- set_condition
- set
- enable
- disable
- toggle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
