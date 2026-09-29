# Recorder Specification

> Tests covering CallEventRecorder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Recorder Specification

## Scenarios

### CallEventRecorder

#### Initialization

#### should create empty recorder

- should create empty recorder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should create empty recorder")
val rec = CallEventRecorder.new("test_case")
expect rec.event_count() == 0
expect rec.current_depth() == 0
```

</details>

#### should store test name

- should store test name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should store test name")
val rec = CallEventRecorder.new("my_test")
expect rec.test_name == "my_test"
```

</details>

#### should start recording by default

- should start recording by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should start recording by default")
val rec = CallEventRecorder.new("test")
expect rec.is_recording == true
```

</details>

#### Recording calls

#### should record a simple function call

- should record a simple function call


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should record a simple function call")
val rec = CallEventRecorder.new("test")
rec.record_call("target_fn", nil, [], CallType.Direct)

expect rec.event_count() == 1
val events = rec.get_events()
expect events[0].callee == "target_fn"
expect events[0].is_return == false
```

</details>

#### should record method call with class

- should record method call with class


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should record method call with class")
val rec = CallEventRecorder.new("test")
rec.record_call("do_work", Some("MyClass"), ["arg1"], CallType.Method)

val events = rec.get_events()
expect events[0].callee == "do_work"
expect events[0].callee_class == Some("MyClass")
expect events[0].call_type == CallType.Method
```

</details>

#### should capture arguments

- should capture arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should capture arguments")
val rec = CallEventRecorder.new("test")
rec.record_call("fn", nil, ["a", "b", "c"], CallType.Direct)

val events = rec.get_events()
expect events[0].arguments.len() == 3
expect events[0].arguments[0] == "a"
expect events[0].arguments[1] == "b"
expect events[0].arguments[2] == "c"
```

</details>

#### should track sequence numbers

- should track sequence numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should track sequence numbers")
val rec = CallEventRecorder.new("test")
rec.record_call("fn1", nil, [], CallType.Direct)
rec.record_call("fn2", nil, [], CallType.Direct)
rec.record_call("fn3", nil, [], CallType.Direct)

val events = rec.get_events()
expect events[0].sequence_num == 0
expect events[1].sequence_num == 1
expect events[2].sequence_num == 2
```

</details>

#### Call stack tracking

#### should track call depth

- should track call depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should track call depth")
val rec = CallEventRecorder.new("test")

# Call at depth 0
rec.record_call("outer", nil, [], CallType.Direct)
expect rec.current_depth() == 1

# Nested call at depth 1
rec.record_call("inner", nil, [], CallType.Direct)
expect rec.current_depth() == 2
```

</details>

#### should record caller from stack

- should record caller from stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should record caller from stack")
val rec = CallEventRecorder.new("test")

rec.record_call("outer", nil, [], CallType.Direct)
rec.record_call("inner", nil, [], CallType.Direct)

val events = rec.get_events()
expect events[0].caller == "(test)"  # No caller for first call
expect events[1].caller == "outer"   # outer called inner
```

</details>

#### should handle return and update depth

- should handle return and update depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should handle return and update depth")
val rec = CallEventRecorder.new("test")

rec.record_call("outer", nil, [], CallType.Direct)
rec.record_call("inner", nil, [], CallType.Direct)
expect rec.current_depth() == 2

rec.record_return(Some("result"))
expect rec.current_depth() == 1
```

</details>

#### Recording returns

#### should record return event

- should record return event


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should record return event")
val rec = CallEventRecorder.new("test")

rec.record_call("fn", nil, [], CallType.Direct)
rec.record_return(Some("42"))

expect rec.event_count() == 2
val events = rec.get_events()
expect events[1].is_return == true
expect events[1].return_value == Some("42")
```

</details>

#### should handle void return

- should handle void return


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should handle void return")
val rec = CallEventRecorder.new("test")

rec.record_call("fn", nil, [], CallType.Direct)
rec.record_return(nil)

val events = rec.get_events()
expect events[1].return_value == nil
```

</details>

#### should match return to correct call

- should match return to correct call


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should match return to correct call")
val rec = CallEventRecorder.new("test")

rec.record_call("outer", nil, [], CallType.Direct)
rec.record_call("inner", nil, [], CallType.Direct)
rec.record_return(Some("inner_result"))

val events = rec.get_events()
expect events[2].callee == "inner"  # Return from inner
```

</details>

#### Class tracking

#### should collect seen classes

- should collect seen classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should collect seen classes")
val rec = CallEventRecorder.new("test")

rec.record_call("method1", Some("ClassA"), [], CallType.Method)
rec.record_call("method2", Some("ClassB"), [], CallType.Method)
rec.record_call("method3", Some("ClassA"), [], CallType.Method)

val classes = rec.get_classes()
expect classes.len() == 2
expect classes.contains("ClassA") == true
expect classes.contains("ClassB") == true
```

</details>

#### Architectural entities

#### should mark entities as architectural

- should mark entities as architectural


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should mark entities as architectural")
val rec = CallEventRecorder.new("test")

rec.mark_architectural("UserService")
rec.mark_architectural("Database")

expect rec.is_architectural("UserService") == true
expect rec.is_architectural("Database") == true
expect rec.is_architectural("SomeClass") == false
```

</details>

#### should return architectural entities set

- should return architectural entities set


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should return architectural entities set")
val rec = CallEventRecorder.new("test")

rec.mark_architectural("Service")
rec.mark_architectural("Repository")

val entities = rec.get_architectural_entities()
expect entities.len() == 2
```

</details>

#### Recording control

#### should stop recording when stopped

- should stop recording when stopped


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should stop recording when stopped")
val rec = CallEventRecorder.new("test")

rec.record_call("fn1", nil, [], CallType.Direct)
rec.stop()
rec.record_call("fn2", nil, [], CallType.Direct)

expect rec.event_count() == 1
```

</details>

#### should resume recording after start

- should resume recording after start


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should resume recording after start")
val rec = CallEventRecorder.new("test")

rec.stop()
rec.start()
rec.record_call("fn", nil, [], CallType.Direct)

expect rec.event_count() == 1
```

</details>

#### should clear all events

- should clear all events


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should clear all events")
val rec = CallEventRecorder.new("test")

rec.record_call("fn1", nil, [], CallType.Direct)
rec.record_call("fn2", nil, [], CallType.Direct)
rec.clear()

expect rec.event_count() == 0
expect rec.get_classes().len() == 0
```

</details>

#### CallEvent formatting

#### should format call with args

- should format call with args


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format call with args")
val event = CallEvent.new_call(
    0, 100, "caller", "target",
    nil, Some("MyClass"),
    ["x", "y"],
    CallType.Method, 0
)

expect event.format_call() == "MyClass.target(x, y)"
```

</details>

#### should format call without class

- should format call without class


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format call without class")
val event = CallEvent.new_call(
    0, 100, "caller", "standalone_fn",
    nil, nil,
    ["arg"],
    CallType.Direct, 0
)

expect event.format_call() == "standalone_fn(arg)"
```

</details>

#### should get participant names

- should get participant names


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should get participant names")
val event = CallEvent.new_call(
    0, 100, "caller", "method",
    Some("CallerClass"), Some("CalleeClass"),
    [],
    CallType.Method, 0
)

expect event.get_caller_participant() == "CallerClass"
expect event.get_callee_participant() == "CalleeClass"
```

</details>

#### should format return value

- should format return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format return value")
val event = CallEvent.new_return(
    0, 100, "caller", "callee",
    nil, nil,
    Some("Result(42)"),
    0
)

expect event.format_return() == "Result(42)"
```

</details>

#### should format void return

- should format void return


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format void return")
val event = CallEvent.new_return(
    0, 100, "caller", "callee",
    nil, nil,
    nil,
    0
)

expect event.format_return() == "(void)"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/diagram/recorder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CallEventRecorder.
- CallEventRecorder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c09d260452c842f2bb86d328bca34803b3bd12a3a4bea180de1ce7f285c5bd5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c09d260452c842f2bb86d328bca34803b3bd12a3a4bea180de1ce7f285c5bd5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c09d260452c842f2bb86d328bca34803b3bd12a3a4bea180de1ce7f285c5bd5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/std/diagram/recorder_spec.spl
mirror: doc/06_spec/01_unit/lib/std/diagram/recorder_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/diagram/recorder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/diagram/recorder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/diagram/recorder_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create empty recorder' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/recorder_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create empty recorder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/diagram/recorder_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should store test name' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/recorder_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should store test name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/diagram/recorder_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should start recording by default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/recorder_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should start recording by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/diagram/recorder_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record a simple function call' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/recorder_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record method call with class' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/recorder_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should capture arguments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
