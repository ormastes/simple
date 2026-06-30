# dap_spec

> DAP Server BDD Specification Tests.

<!-- sdn-diagram:id=dap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dap_spec

DAP Server BDD Specification Tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | Active |
| Source | `test/03_system/tools/dap/dap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DAP Server BDD Specification Tests.
Validates Debug Adapter Protocol functionality including events,
breakpoints, stack frames, threads, variables, and launch configuration.

## Scenarios

### DAP Event Handling

#### should identify event types with pattern matching

1. expect get event type
2. expect get event type
3. expect get event type
4. expect get event type


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stopped = DapEvent.Stopped(reason: "breakpoint", thread_id: 1)
val continued = DapEvent.Continued(thread_id: 1)
val terminated = DapEvent.Terminated
val exited = DapEvent.Exited(exit_code: 0)

expect get_event_type(stopped) == "stopped"
expect get_event_type(continued) == "continued"
expect get_event_type(terminated) == "terminated"
expect get_event_type(exited) == "exited"
```

</details>

#### should determine if event requires response

1. expect requires response
2. expect requires response
3. expect requires response


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stopped = DapEvent.Stopped(reason: "breakpoint", thread_id: 1)
val output = DapEvent.Output(category: "stdout", output: "Hello")
val breakpoint_event = DapEvent.Breakpoint(breakpoint_id: 1)

expect requires_response(stopped) == true
expect requires_response(output) == false
expect requires_response(breakpoint_event) == true
```

</details>

#### should extract data from stopped event

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = DapEvent.Stopped(reason: "breakpoint", thread_id: 5)

match event:
    case Stopped(reason, thread_id):
        expect reason == "breakpoint"
        expect thread_id == 5
    case _:
        fail "Should be stopped event"
```

</details>

### DAP Breakpoint Management

#### should create and validate breakpoints

1. expect is valid breakpoint
2. expect is valid breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_bp = Breakpoint {
    id: 1,
    location: SourceLocation { path: "test.spl", line: 10, column: 0 },
    state: BreakpointState.Verified,
    condition: "",
    hit_count: 0
}

val invalid_bp = Breakpoint {
    id: 2,
    location: SourceLocation { path: "", line: 0, column: 0 },
    state: BreakpointState.Pending,
    condition: "",
    hit_count: 0
}

expect is_valid_breakpoint(valid_bp) == true
expect is_valid_breakpoint(invalid_bp) == false
```

</details>

#### should count verified breakpoints

1. expect count verified breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val breakpoints = [
    Breakpoint {
        id: 1,
        location: SourceLocation { path: "test.spl", line: 10, column: 0 },
        state: BreakpointState.Verified,
        condition: "",
        hit_count: 0
    },
    Breakpoint {
        id: 2,
        location: SourceLocation { path: "test.spl", line: 20, column: 0 },
        state: BreakpointState.Pending,
        condition: "",
        hit_count: 0
    },
    Breakpoint {
        id: 3,
        location: SourceLocation { path: "test.spl", line: 30, column: 0 },
        state: BreakpointState.Verified,
        condition: "",
        hit_count: 0
    }
]

expect count_verified_breakpoints(breakpoints) == 2
```

</details>

#### should filter verified breakpoints

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val breakpoints = [
    Breakpoint {
        id: 1,
        location: SourceLocation { path: "test.spl", line: 10, column: 0 },
        state: BreakpointState.Verified,
        condition: "",
        hit_count: 0
    },
    Breakpoint {
        id: 2,
        location: SourceLocation { path: "test.spl", line: 20, column: 0 },
        state: BreakpointState.Failed,
        condition: "",
        hit_count: 0
    }
]

val verified = filter_verified_breakpoints(breakpoints)
expect len(verified) == 1
expect verified[0].state == BreakpointState.Verified
```

</details>

#### should handle empty breakpoint list

1. expect count verified breakpoints
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val breakpoints = []

expect count_verified_breakpoints(breakpoints) == 0
expect len(filter_verified_breakpoints(breakpoints)) == 0
```

</details>

### DAP Stack Frames

#### should create stack frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = StackFrame {
    id: 0,
    name: "main",
    location: SourceLocation { path: "main.spl", line: 42, column: 5 }
}

expect frame.id == 0
expect frame.name == "main"
expect frame.location.line == 42
```

</details>

#### should format stack frame for display

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = StackFrame {
    id: 0,
    name: "calculate",
    location: SourceLocation { path: "math.spl", line: 100, column: 10 }
}

val formatted = format_stack_frame(frame)
expect formatted == "calculate at math.spl"
```

</details>

#### should create stack trace

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frames = [
    StackFrame {
        id: 0,
        name: "inner",
        location: SourceLocation { path: "test.spl", line: 10, column: 0 }
    },
    StackFrame {
        id: 1,
        name: "middle",
        location: SourceLocation { path: "test.spl", line: 20, column: 0 }
    },
    StackFrame {
        id: 2,
        name: "outer",
        location: SourceLocation { path: "test.spl", line: 30, column: 0 }
    }
]

expect len(frames) == 3
expect frames[0].name == "inner"
expect frames[2].name == "outer"
```

</details>

### DAP Thread Management

#### should create thread info

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val thread = ThreadInfo {
    id: 1,
    name: "Main Thread",
    state: ThreadState.Running
}

expect thread.id == 1
expect thread.name == "Main Thread"
expect thread.state == ThreadState.Running
```

</details>

#### should check thread state

1. expect is thread stopped
2. expect is thread stopped


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val running_thread = ThreadInfo {
    id: 1,
    name: "Thread 1",
    state: ThreadState.Running
}

val stopped_thread = ThreadInfo {
    id: 2,
    name: "Thread 2",
    state: ThreadState.Stopped
}

expect is_thread_stopped(running_thread) == false
expect is_thread_stopped(stopped_thread) == true
```

</details>

#### should extract thread IDs

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val threads = [
    ThreadInfo { id: 1, name: "Thread 1", state: ThreadState.Running },
    ThreadInfo { id: 2, name: "Thread 2", state: ThreadState.Stopped },
    ThreadInfo { id: 3, name: "Thread 3", state: ThreadState.Running }
]

val ids = extract_thread_ids(threads)
expect len(ids) == 3
expect ids[0] == 1
expect ids[1] == 2
expect ids[2] == 3
```

</details>

#### should count threads by state

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val threads = [
    ThreadInfo { id: 1, name: "T1", state: ThreadState.Running },
    ThreadInfo { id: 2, name: "T2", state: ThreadState.Stopped },
    ThreadInfo { id: 3, name: "T3", state: ThreadState.Running }
]

var stopped_count = 0
for thread in threads:
    if is_thread_stopped(thread):
        stopped_count = stopped_count + 1

expect stopped_count == 1
```

</details>

### DAP Variable Inspection

#### should create variable info

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val var_info = Variable {
    name: "x",
    value: "42",
    value_type: "i64"
}

expect var_info.name == "x"
expect var_info.value == "42"
expect var_info.value_type == "i64"
```

</details>

#### should represent different types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val int_var = Variable { name: "count", value: "10", value_type: "i64" }
val str_var = Variable { name: "message", value: "hello", value_type: "str" }
val bool_var = Variable { name: "flag", value: "true", value_type: "bool" }

expect int_var.value_type == "i64"
expect str_var.value_type == "str"
expect bool_var.value_type == "bool"
```

</details>

#### should collect variables in scope

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variables = [
    Variable { name: "x", value: "1", value_type: "i64" },
    Variable { name: "y", value: "2", value_type: "i64" },
    Variable { name: "result", value: "3", value_type: "i64" }
]

expect len(variables) == 3
expect variables[0].name == "x"
```

</details>

### DAP Launch Configuration

#### should create launch configuration

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig {
    program: "/path/to/program.spl",
    args: ["--verbose", "--debug"],
    cwd: "/workspace",
    stop_on_entry: true
}

expect config.program == "/path/to/program.spl"
expect len(config.args) == 2
expect config.cwd == "/workspace"
expect config.stop_on_entry == true
```

</details>

#### should handle empty arguments

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig {
    program: "app.spl",
    args: [],
    cwd: ".",
    stop_on_entry: false
}

expect len(config.args) == 0
expect config.stop_on_entry == false
```

</details>

#### should validate program path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig {
    program: "test.spl",
    args: [],
    cwd: ".",
    stop_on_entry: false
}

expect config.program != ""
```

</details>

### DAP Event Processing

#### should process array of events

1. DapEvent Stopped
2. DapEvent Output
3. DapEvent Continued


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = [
    DapEvent.Stopped(reason: "breakpoint", thread_id: 1),
    DapEvent.Output(category: "stdout", output: "Debug message"),
    DapEvent.Continued(thread_id: 1)
]

var response_required_count = 0
for event in events:
    if requires_response(event):
        response_required_count = response_required_count + 1

expect response_required_count == 1
```

</details>

#### should collect event types

1. DapEvent Stopped
2. DapEvent Continued
3. DapEvent Exited
4. types push
5. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = [
    DapEvent.Stopped(reason: "breakpoint", thread_id: 1),
    DapEvent.Continued(thread_id: 1),
    DapEvent.Exited(exit_code: 0)
]

var types = []
for event in events:
    types.push(get_event_type(event))

expect len(types) == 3
expect types[0] == "stopped"
expect types[1] == "continued"
expect types[2] == "exited"
```

</details>

#### should handle terminal events

1. expect get event type
2. expect get event type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val terminated = DapEvent.Terminated
val exited = DapEvent.Exited(exit_code: 0)
expect get_event_type(terminated) == "terminated"
expect get_event_type(exited) == "exited"
```

</details>

### DAP Breakpoint States

#### should transition breakpoint states

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp_pending = Breakpoint {
    id: 1,
    location: SourceLocation { path: "test.spl", line: 10, column: 0 },
    state: BreakpointState.Pending,
    condition: "",
    hit_count: 0
}

# Simulate state transition by creating new breakpoint
val bp_verified = Breakpoint {
    id: 1,
    location: SourceLocation { path: "test.spl", line: 10, column: 0 },
    state: BreakpointState.Verified,
    condition: "",
    hit_count: 1
}

expect bp_pending.state == BreakpointState.Pending
expect bp_verified.state == BreakpointState.Verified
```

</details>

#### should track breakpoint lifecycle

1. state list push
2. state list push
3. state list push
4. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val states = []
var state_list = []

state_list.push(BreakpointState.Pending)
state_list.push(BreakpointState.Verified)
state_list.push(BreakpointState.Failed)

expect len(state_list) == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
