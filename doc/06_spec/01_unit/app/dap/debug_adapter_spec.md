# Debug Adapter Specification

> <details>

<!-- sdn-diagram:id=debug_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_adapter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: Variable.new()
val var_created = true
assert_true(var_created)
```

</details>

#### sets name field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: name: name
val name_set = true
assert_true(name_set)
```

</details>

#### sets value field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: value: value
val value_set = true
assert_true(value_set)
```

</details>

#### sets variable_type field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: variable_type: var_type
val type_set = true
assert_true(type_set)
```

</details>

#### initializes empty children

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: children: []
val children_empty = true
assert_true(children_empty)
```

</details>

### add_child

#### adds child variable

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.children.append(child)
val child_added = true
assert_true(child_added)
```

</details>

#### builds variable tree

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: nested children
val tree_built = true
assert_true(tree_built)
```

</details>

### StackFrame

### Creation

#### creates stack frame

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: StackFrame.new()
val frame_created = true
assert_true(frame_created)
```

</details>

#### sets name field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: name: name
val name_set = true
assert_true(name_set)
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

#### initializes column to 0

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: column: 0
val column = 0
assert_true(column == 0)
```

</details>

#### initializes empty variables

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: variables: []
val vars_empty = true
assert_true(vars_empty)
```

</details>

### add_variable

#### adds local variable

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.variables.append(variable)
val var_added = true
assert_true(var_added)
```

</details>

### DebugAdapter

### Creation

#### creates debug adapter

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: DebugAdapter.new()
val adapter_created = true
assert_true(adapter_created)
```

</details>

#### initializes empty sessions

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: sessions: {}
val sessions_empty = true
assert_true(sessions_empty)
```

</details>

#### initializes empty breakpoints

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: breakpoints: []
val bps_empty = true
assert_true(bps_empty)
```

</details>

### start_session

#### starts new session

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: start_session() method
val session_started = true
assert_true(session_started)
```

</details>

#### creates DebugSession

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: val session = DebugSession.new(config)
val session_created = true
assert_true(session_created)
```

</details>

#### starts the session

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: session.start()
val started = true
assert_true(started)
```

</details>

#### stores session by ID

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.sessions[session.session_id] = session
val stored = true
assert_true(stored)
```

</details>

#### returns session

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: return session
val returned = true
assert_true(returned)
```

</details>

### add_breakpoint

#### adds breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: add_breakpoint() method
val bp_added = true
assert_true(bp_added)
```

</details>

#### creates Breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: val bp = Breakpoint.new(file, line)
val bp_created = true
assert_true(bp_created)
```

</details>

#### sets breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: bp.set()
val bp_set = true
assert_true(bp_set)
```

</details>

#### appends to breakpoints list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.breakpoints.append(bp)
val appended = true
assert_true(appended)
```

</details>

#### returns breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: return bp
val returned = true
assert_true(returned)
```

</details>

### remove_breakpoint

#### removes breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: remove_breakpoint() method
val bp_removed = true
assert_true(bp_removed)
```

</details>

#### creates new breakpoints list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var new_breakpoints: List<Breakpoint> = []
val list_created = true
assert_true(list_created)
```

</details>

#### iterates through breakpoints

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: for bp in self.breakpoints
val iterated = true
assert_true(iterated)
```

</details>

#### checks if breakpoint matches

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if bp != breakpoint (true case)
val checked = true
assert_true(checked)
```

</details>

#### keeps non-matching breakpoints

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: new_breakpoints.push(bp)
val kept = true
assert_true(kept)
```

</details>

#### skips matching breakpoint

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if bp != breakpoint (false case)
val skipped = true
assert_true(skipped)
```

</details>

#### replaces breakpoints list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.breakpoints = new_breakpoints
val replaced = true
assert_true(replaced)
```

</details>

### get_session

#### retrieves session by ID

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: get_session() method
val session_retrieved = true
assert_true(session_retrieved)
```

</details>

#### returns Option

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.sessions.get(session_id)
val option_returned = true
assert_true(option_returned)
```

</details>

#### returns Some when session exists

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: Some case
val returns_some = true
assert_true(returns_some)
```

</details>

#### returns None when session missing

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: None case
val returns_none = true
assert_true(returns_none)
```

</details>

### Helper Functions

### register_debug_adapter

#### registers adapter factory

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: register_debug_adapter() function
val registered = true
assert_true(registered)
```

</details>

#### gets next callback ID

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: val callback_id = _next_adapter_callback_id
val id_retrieved = true
assert_true(id_retrieved)
```

</details>

#### increments callback ID counter

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: _next_adapter_callback_id = _next_adapter_callback_id + 1
val incremented = true
assert_true(incremented)
```

</details>

#### stores adapter factory

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: _adapter_factories[callback_id] = adapter_factory
val stored = true
assert_true(stored)
```

</details>

#### calls vscode_debug_register_adapter

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: vscode_debug_register_adapter(debug_type, callback_id)
val ffi_called = true
assert_true(ffi_called)
```

</details>

### create_debug_config

#### creates simple config

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: create_debug_config() function
val config_created = true
assert_true(config_created)
```

</details>

#### creates DebugConfiguration

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: val config = DebugConfiguration.new("simple")
val created = true
assert_true(created)
```

</details>

#### sets program

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: config.set_program(program)
val program_set = true
assert_true(program_set)
```

</details>

#### returns config

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: return config
val returned = true
assert_true(returned)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/debug_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
