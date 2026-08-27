# dap_spec

> DAP Server BDD Specification Tests.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DAP Server BDD Specification Tests.
Validates Debug Adapter Protocol functionality including events,
breakpoints, stack frames, threads, variables, and launch configuration.

## Scenarios

### DAP Event Handling

#### should identify event types with pattern matching

- should identify event types with pattern matching


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should identify event types with pattern matching")
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

- should determine if event requires response


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should determine if event requires response")
val stopped = DapEvent.Stopped(reason: "breakpoint", thread_id: 1)
val output = DapEvent.Output(category: "stdout", output: "Hello")
val breakpoint_event = DapEvent.Breakpoint(breakpoint_id: 1)

expect requires_response(stopped) == true
expect requires_response(output) == false
expect requires_response(breakpoint_event) == true
```

</details>

#### should extract data from stopped event

- should extract data from stopped event


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should extract data from stopped event")
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

- should create and validate breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create and validate breakpoints")
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

- should count verified breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should count verified breakpoints")
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

- should filter verified breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filter verified breakpoints")
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

- should handle empty breakpoint list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle empty breakpoint list")
val breakpoints = []

expect count_verified_breakpoints(breakpoints) == 0
expect len(filter_verified_breakpoints(breakpoints)) == 0
```

</details>

### DAP Stack Frames

#### should create stack frames

- should create stack frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create stack frames")
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

- should format stack frame for display


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should format stack frame for display")
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

- should create stack trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create stack trace")
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

- should create thread info


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create thread info")
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

- should check thread state


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should check thread state")
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

- should extract thread IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should extract thread IDs")
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

- should count threads by state


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should count threads by state")
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

- should create variable info


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create variable info")
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

- should represent different types


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should represent different types")
val int_var = Variable { name: "count", value: "10", value_type: "i64" }
val str_var = Variable { name: "message", value: "hello", value_type: "str" }
val bool_var = Variable { name: "flag", value: "true", value_type: "bool" }

expect int_var.value_type == "i64"
expect str_var.value_type == "str"
expect bool_var.value_type == "bool"
```

</details>

#### should collect variables in scope

- should collect variables in scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should collect variables in scope")
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

- should create launch configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create launch configuration")
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

- should handle empty arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle empty arguments")
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

- should validate program path


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate program path")
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

- should process array of events


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should process array of events")
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

- should collect event types


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should collect event types")
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

- should handle terminal events


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle terminal events")
val terminated = DapEvent.Terminated
val exited = DapEvent.Exited(exit_code: 0)
expect get_event_type(terminated) == "terminated"
expect get_event_type(exited) == "exited"
```

</details>

### DAP Breakpoint States

#### should transition breakpoint states

- should transition breakpoint states


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should transition breakpoint states")
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

- should track breakpoint lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should track breakpoint lifecycle")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c7f8bccbbe2636e72700536894b4fa90c4a284508086925a79d4407a207c42d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7f8bccbbe2636e72700536894b4fa90c4a284508086925a79d4407a207c42d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7f8bccbbe2636e72700536894b4fa90c4a284508086925a79d4407a207c42d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/dap/dap_spec.spl
mirror: doc/06_spec/03_system/tools/dap/dap_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/dap/dap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/dap/dap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/dap/dap_spec.spl:172:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should identify event types with pattern matching' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/dap/dap_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should identify event types with pattern matching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/dap/dap_spec.spl:185:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should determine if event requires response' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/dap/dap_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should determine if event requires response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/dap/dap_spec.spl:196:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract data from stopped event' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/dap/dap_spec.spl:196:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract data from stopped event' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/dap/dap_spec.spl:215:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create and validate breakpoints' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/dap/dap_spec.spl:237:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should count verified breakpoints' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/dap/dap_spec.spl:266:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should filter verified breakpoints' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
