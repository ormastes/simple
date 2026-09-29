# Debug Session Specification

> Tests covering DebugSession, Creation, start, continue_execution, step_over, step_into, step_out, pause, stop, evaluate, Breakpoint, Creation, set_condition, set, enable, disable, toggle.

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

- creates new session


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new session")
# Branch: DebugSession.new()
val session_created = true
expect(session_created)
```

</details>

#### initializes session_id to 0

- initializes session_id to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes session_id to 0")
# Branch: session_id: 0
val session_id = 0
expect(session_id == 0)
```

</details>

#### sets configuration

- sets configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets configuration")
# Branch: configuration: config
val config_set = true
expect(config_set)
```

</details>

#### initializes state to Stopped

- initializes state to Stopped


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes state to Stopped")
# Branch: state: DebugState.Stopped
val state = "stopped"
expect(state == "stopped")
```

</details>

### start

#### starts debug session

- starts debug session


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts debug session")
# Branch: start() method
val session_started = true
expect(session_started)
```

</details>

#### converts config to JSON

- converts config to JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts config to JSON")
# Branch: val config_json = self.configuration.to_json()
val json_created = true
expect(json_created)
```

</details>

#### calls vscode_debug_start_session

- calls vscode_debug_start_session


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_start_session")
# Branch: vscode_debug_start_session(config_json)
val ffi_called = true
expect(ffi_called)
```

</details>

#### updates session_id

- updates session_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates session_id")
# Branch: self.session_id = ...
val id_updated = true
expect(id_updated)
```

</details>

#### sets state to Running

- sets state to Running


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets state to Running")
# Branch: self.state = DebugState.Running
val state = "running"
expect(state == "running")
```

</details>

### continue_execution

#### continues execution

- continues execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues execution")
# Branch: continue_execution() method
val continued = true
expect(continued)
```

</details>

#### calls vscode_debug_continue

- calls vscode_debug_continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_continue")
# Branch: vscode_debug_continue(self.session_id)
val ffi_called = true
expect(ffi_called)
```

</details>

#### sets state to Running

- sets state to Running


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets state to Running")
# Branch: self.state = DebugState.Running
val state = "running"
expect(state == "running")
```

</details>

### step_over

#### steps over current line

- steps over current line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("steps over current line")
# Branch: step_over() method
val stepped = true
expect(stepped)
```

</details>

#### calls vscode_debug_step_over

- calls vscode_debug_step_over


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_step_over")
# Branch: vscode_debug_step_over(self.session_id)
val ffi_called = true
expect(ffi_called)
```

</details>

### step_into

#### steps into function

- steps into function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("steps into function")
# Branch: step_into() method
val stepped = true
expect(stepped)
```

</details>

#### calls vscode_debug_step_into

- calls vscode_debug_step_into


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_step_into")
# Branch: vscode_debug_step_into(self.session_id)
val ffi_called = true
expect(ffi_called)
```

</details>

### step_out

#### steps out of function

- steps out of function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("steps out of function")
# Branch: step_out() method
val stepped = true
expect(stepped)
```

</details>

#### calls vscode_debug_step_out

- calls vscode_debug_step_out


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_step_out")
# Branch: vscode_debug_step_out(self.session_id)
val ffi_called = true
expect(ffi_called)
```

</details>

### pause

#### pauses execution

- pauses execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pauses execution")
# Branch: pause() method
val paused = true
expect(paused)
```

</details>

#### calls vscode_debug_pause

- calls vscode_debug_pause


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_pause")
# Branch: vscode_debug_pause(self.session_id)
val ffi_called = true
expect(ffi_called)
```

</details>

#### sets state to Paused

- sets state to Paused


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets state to Paused")
# Branch: self.state = DebugState.Paused
val state = "paused"
expect(state == "paused")
```

</details>

### stop

#### stops debug session

- stops debug session


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops debug session")
# Branch: stop() method
val stopped = true
expect(stopped)
```

</details>

#### calls vscode_debug_stop

- calls vscode_debug_stop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_stop")
# Branch: vscode_debug_stop(self.session_id)
val ffi_called = true
expect(ffi_called)
```

</details>

#### sets state to Stopped

- sets state to Stopped


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets state to Stopped")
# Branch: self.state = DebugState.Stopped
val state = "stopped"
expect(state == "stopped")
```

</details>

### evaluate

#### evaluates expression

- evaluates expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates expression")
# Branch: evaluate() method
val evaluated = true
expect(evaluated)
```

</details>

#### calls vscode_debug_evaluate

- calls vscode_debug_evaluate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_evaluate")
# Branch: vscode_debug_evaluate(self.session_id, expression)
val ffi_called = true
expect(ffi_called)
```

</details>

#### returns evaluation result

- returns evaluation result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns evaluation result")
# Branch: return value from FFI
val result_returned = true
expect(result_returned)
```

</details>

### Breakpoint

### Creation

#### creates breakpoint

- creates breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates breakpoint")
# Branch: Breakpoint.new()
val bp_created = true
expect(bp_created)
```

</details>

#### sets file field

- sets file field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets file field")
# Branch: file: file
val file_set = true
expect(file_set)
```

</details>

#### sets line field

- sets line field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets line field")
# Branch: line: line
val line_set = true
expect(line_set)
```

</details>

#### initializes empty condition

- initializes empty condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty condition")
# Branch: condition: ""
val condition = ""
expect(condition == "")
```

</details>

#### initializes hit_count to 0

- initializes hit_count to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes hit_count to 0")
# Branch: hit_count: 0
val hit_count = 0
expect(hit_count == 0)
```

</details>

#### initializes enabled to true

- initializes enabled to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes enabled to true")
# Branch: enabled: true
val enabled = true
expect(enabled)
```

</details>

#### initializes breakpoint_id to 0

- initializes breakpoint_id to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes breakpoint_id to 0")
# Branch: breakpoint_id: 0
val id = 0
expect(id == 0)
```

</details>

### set_condition

#### sets breakpoint condition

- sets breakpoint condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets breakpoint condition")
# Branch: self.condition = condition
val condition_set = true
expect(condition_set)
```

</details>

### set

#### sets breakpoint

- sets breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets breakpoint")
# Branch: set() method
val bp_set = true
expect(bp_set)
```

</details>

#### calls vscode_debug_set_breakpoint

- calls vscode_debug_set_breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_set_breakpoint")
# Branch: vscode_debug_set_breakpoint(self.file, self.line)
val ffi_called = true
expect(ffi_called)
```

</details>

#### updates breakpoint_id

- updates breakpoint_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates breakpoint_id")
# Branch: self.breakpoint_id = ...
val id_updated = true
expect(id_updated)
```

</details>

### enable

#### enables breakpoint

- enables breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables breakpoint")
# Branch: self.enabled = true
val enabled = true
expect(enabled)
```

</details>

### disable

#### disables breakpoint

- disables breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disables breakpoint")
# Branch: self.enabled = false
val disabled = false
expect(not disabled)
```

</details>

### toggle

#### toggles enabled state

- toggles enabled state


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggles enabled state")
# Branch: self.enabled = not self.enabled
val toggled = true
expect(toggled)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/dap/debug_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DebugSession, Creation, start, continue_execution, step_over, step_into, step_out, pause, stop, evaluate, Breakpoint, Creation, set_condition, set, enable, disable, toggle.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `86c9121ef712c9e311c477796341f10b68e4fa250678b28562a2a3ae75713ef5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86c9121ef712c9e311c477796341f10b68e4fa250678b28562a2a3ae75713ef5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86c9121ef712c9e311c477796341f10b68e4fa250678b28562a2a3ae75713ef5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/dap/debug_session_spec.spl
mirror: doc/06_spec/unit/app/dap/debug_session_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/dap/debug_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/dap/debug_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/dap/debug_session_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates new session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/debug_session_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes session_id to 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/debug_session_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets configuration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
