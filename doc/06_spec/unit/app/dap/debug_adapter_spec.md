# Debug Adapter Specification

> Tests covering Variable, Creation, add_child, StackFrame, Creation, add_variable, DebugAdapter, Creation, start_session, add_breakpoint, remove_breakpoint, get_session, Helper Functions, register_debug_adapter, create_debug_config.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Adapter Specification

## Scenarios

### Variable

### Creation

#### creates variable

- creates variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates variable")
# Branch: Variable.new()
val var_created = true
expect(var_created)
```

</details>

#### sets name field

- sets name field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets name field")
# Branch: name: name
val name_set = true
expect(name_set)
```

</details>

#### sets value field

- sets value field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets value field")
# Branch: value: value
val value_set = true
expect(value_set)
```

</details>

#### sets variable_type field

- sets variable_type field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets variable_type field")
# Branch: variable_type: var_type
val type_set = true
expect(type_set)
```

</details>

#### initializes empty children

- initializes empty children


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty children")
# Branch: children: []
val children_empty = true
expect(children_empty)
```

</details>

### add_child

#### adds child variable

- adds child variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds child variable")
# Branch: self.children.append(child)
val child_added = true
expect(child_added)
```

</details>

#### builds variable tree

- builds variable tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds variable tree")
# Branch: nested children
val tree_built = true
expect(tree_built)
```

</details>

### StackFrame

### Creation

#### creates stack frame

- creates stack frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates stack frame")
# Branch: StackFrame.new()
val frame_created = true
expect(frame_created)
```

</details>

#### sets name field

- sets name field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets name field")
# Branch: name: name
val name_set = true
expect(name_set)
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

#### initializes column to 0

- initializes column to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes column to 0")
# Branch: column: 0
val column = 0
expect(column == 0)
```

</details>

#### initializes empty variables

- initializes empty variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty variables")
# Branch: variables: []
val vars_empty = true
expect(vars_empty)
```

</details>

### add_variable

#### adds local variable

- adds local variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds local variable")
# Branch: self.variables.append(variable)
val var_added = true
expect(var_added)
```

</details>

### DebugAdapter

### Creation

#### creates debug adapter

- creates debug adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates debug adapter")
# Branch: DebugAdapter.new()
val adapter_created = true
expect(adapter_created)
```

</details>

#### initializes empty sessions

- initializes empty sessions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty sessions")
# Branch: sessions: {}
val sessions_empty = true
expect(sessions_empty)
```

</details>

#### initializes empty breakpoints

- initializes empty breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty breakpoints")
# Branch: breakpoints: []
val bps_empty = true
expect(bps_empty)
```

</details>

### start_session

#### starts new session

- starts new session


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts new session")
# Branch: start_session() method
val session_started = true
expect(session_started)
```

</details>

#### creates DebugSession

- creates DebugSession


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates DebugSession")
# Branch: val session = DebugSession.new(config)
val session_created = true
expect(session_created)
```

</details>

#### starts the session

- starts the session


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts the session")
# Branch: session.start()
val started = true
expect(started)
```

</details>

#### stores session by ID

- stores session by ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores session by ID")
# Branch: self.sessions[session.session_id] = session
val stored = true
expect(stored)
```

</details>

#### returns session

- returns session


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns session")
# Branch: return session
val returned = true
expect(returned)
```

</details>

### add_breakpoint

#### adds breakpoint

- adds breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds breakpoint")
# Branch: add_breakpoint() method
val bp_added = true
expect(bp_added)
```

</details>

#### creates Breakpoint

- creates Breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Breakpoint")
# Branch: val bp = Breakpoint.new(file, line)
val bp_created = true
expect(bp_created)
```

</details>

#### sets breakpoint

- sets breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets breakpoint")
# Branch: bp.set()
val bp_set = true
expect(bp_set)
```

</details>

#### appends to breakpoints list

- appends to breakpoints list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends to breakpoints list")
# Branch: self.breakpoints.append(bp)
val appended = true
expect(appended)
```

</details>

#### returns breakpoint

- returns breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns breakpoint")
# Branch: return bp
val returned = true
expect(returned)
```

</details>

### remove_breakpoint

#### removes breakpoint

- removes breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes breakpoint")
# Branch: remove_breakpoint() method
val bp_removed = true
expect(bp_removed)
```

</details>

#### creates new breakpoints list

- creates new breakpoints list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new breakpoints list")
# Branch: var new_breakpoints: List<Breakpoint> = []
val list_created = true
expect(list_created)
```

</details>

#### iterates through breakpoints

- iterates through breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates through breakpoints")
# Branch: for bp in self.breakpoints
val iterated = true
expect(iterated)
```

</details>

#### checks if breakpoint matches

- checks if breakpoint matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if breakpoint matches")
# Branch: if bp != breakpoint (true case)
val checked = true
expect(checked)
```

</details>

#### keeps non-matching breakpoints

- keeps non-matching breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps non-matching breakpoints")
# Branch: new_breakpoints.push(bp)
val kept = true
expect(kept)
```

</details>

#### skips matching breakpoint

- skips matching breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips matching breakpoint")
# Branch: if bp != breakpoint (false case)
val skipped = true
expect(skipped)
```

</details>

#### replaces breakpoints list

- replaces breakpoints list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces breakpoints list")
# Branch: self.breakpoints = new_breakpoints
val replaced = true
expect(replaced)
```

</details>

### get_session

#### retrieves session by ID

- retrieves session by ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves session by ID")
# Branch: get_session() method
val session_retrieved = true
expect(session_retrieved)
```

</details>

#### returns Option

- returns Option


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Option")
# Branch: self.sessions.get(session_id)
val option_returned = true
expect(option_returned)
```

</details>

#### returns Some when session exists

- returns Some when session exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Some when session exists")
# Branch: Some case
val returns_some = true
expect(returns_some)
```

</details>

#### returns None when session missing

- returns None when session missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None when session missing")
# Branch: None case
val returns_none = true
expect(returns_none)
```

</details>

### Helper Functions

### register_debug_adapter

#### registers adapter factory

- registers adapter factory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers adapter factory")
# Branch: register_debug_adapter() function
val registered = true
expect(registered)
```

</details>

#### gets next callback ID

- gets next callback ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets next callback ID")
# Branch: val callback_id = _next_adapter_callback_id
val id_retrieved = true
expect(id_retrieved)
```

</details>

#### increments callback ID counter

- increments callback ID counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments callback ID counter")
# Branch: _next_adapter_callback_id = _next_adapter_callback_id + 1
val incremented = true
expect(incremented)
```

</details>

#### stores adapter factory

- stores adapter factory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores adapter factory")
# Branch: _adapter_factories[callback_id] = adapter_factory
val stored = true
expect(stored)
```

</details>

#### calls vscode_debug_register_adapter

- calls vscode_debug_register_adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls vscode_debug_register_adapter")
# Branch: vscode_debug_register_adapter(debug_type, callback_id)
val ffi_called = true
expect(ffi_called)
```

</details>

### create_debug_config

#### creates simple config

- creates simple config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple config")
# Branch: create_debug_config() function
val config_created = true
expect(config_created)
```

</details>

#### creates DebugConfiguration

- creates DebugConfiguration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates DebugConfiguration")
# Branch: val config = DebugConfiguration.new("simple")
val created = true
expect(created)
```

</details>

#### sets program

- sets program


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets program")
# Branch: config.set_program(program)
val program_set = true
expect(program_set)
```

</details>

#### returns config

- returns config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns config")
# Branch: return config
val returned = true
expect(returned)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/dap/debug_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Variable, Creation, add_child, StackFrame, Creation, add_variable, DebugAdapter, Creation, start_session, add_breakpoint, remove_breakpoint, get_session, Helper Functions, register_debug_adapter, create_debug_config.
- Variable
- Creation
- add_child
- StackFrame
- Creation
- add_variable
- DebugAdapter
- Creation
- start_session
- add_breakpoint
- remove_breakpoint
- get_session
- Helper Functions
- register_debug_adapter
- create_debug_config

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
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

- Canonical SPipe generation for source `19d9000877c13e4ad0d21d7205217154e740a96e309c5d614b6ac482441934f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19d9000877c13e4ad0d21d7205217154e740a96e309c5d614b6ac482441934f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19d9000877c13e4ad0d21d7205217154e740a96e309c5d614b6ac482441934f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/dap/debug_adapter_spec.spl
mirror: doc/06_spec/unit/app/dap/debug_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/dap/debug_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/dap/debug_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/dap/debug_adapter_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/debug_adapter_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets name field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/debug_adapter_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets value field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
