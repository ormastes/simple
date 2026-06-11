# Recorder Specification

> 1. expect rec event count

<!-- sdn-diagram:id=recorder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=recorder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

recorder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=recorder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. expect rec event count
2. expect rec current depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test_case")
expect rec.event_count() == 0
expect rec.current_depth() == 0
```

</details>

#### should store test name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("my_test")
expect rec.test_name == "my_test"
```

</details>

#### should start recording by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
expect rec.is_recording == true
```

</details>

#### Recording calls

#### should record a simple function call

1. rec record call
2. expect rec event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("target_fn", nil, [], CallType.Direct)

expect rec.event_count() == 1
val events = rec.get_events()
expect events[0].callee == "target_fn"
expect events[0].is_return == false
```

</details>

#### should record method call with class

1. rec record call
2. expect events[0] callee class == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("do_work", Some("MyClass"), ["arg1"], CallType.Method)

val events = rec.get_events()
expect events[0].callee == "do_work"
expect events[0].callee_class == Some("MyClass")
expect events[0].call_type == CallType.Method
```

</details>

#### should capture arguments

1. rec record call
2. expect events[0] arguments len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rec record call
2. rec record call
3. rec record call


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rec record call
2. expect rec current depth
3. rec record call
4. expect rec current depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rec record call
2. rec record call
3. expect events[0] caller == "


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")

rec.record_call("outer", nil, [], CallType.Direct)
rec.record_call("inner", nil, [], CallType.Direct)

val events = rec.get_events()
expect events[0].caller == "(test)"  # No caller for first call
expect events[1].caller == "outer"   # outer called inner
```

</details>

#### should handle return and update depth

1. rec record call
2. rec record call
3. expect rec current depth
4. rec record return
5. expect rec current depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rec record call
2. rec record return
3. expect rec event count
4. expect events[1] return value == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rec record call
2. rec record return


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")

rec.record_call("fn", nil, [], CallType.Direct)
rec.record_return(nil)

val events = rec.get_events()
expect events[1].return_value == nil
```

</details>

#### should match return to correct call

1. rec record call
2. rec record call
3. rec record return


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rec record call
2. rec record call
3. rec record call
4. expect classes len
5. expect classes contains
6. expect classes contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rec mark architectural
2. rec mark architectural
3. expect rec is architectural
4. expect rec is architectural
5. expect rec is architectural


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")

rec.mark_architectural("UserService")
rec.mark_architectural("Database")

expect rec.is_architectural("UserService") == true
expect rec.is_architectural("Database") == true
expect rec.is_architectural("SomeClass") == false
```

</details>

#### should return architectural entities set

1. rec mark architectural
2. rec mark architectural
3. expect entities len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")

rec.mark_architectural("Service")
rec.mark_architectural("Repository")

val entities = rec.get_architectural_entities()
expect entities.len() == 2
```

</details>

#### Recording control

#### should stop recording when stopped

1. rec record call
2. rec stop
3. rec record call
4. expect rec event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")

rec.record_call("fn1", nil, [], CallType.Direct)
rec.stop()
rec.record_call("fn2", nil, [], CallType.Direct)

expect rec.event_count() == 1
```

</details>

#### should resume recording after start

1. rec stop
2. rec start
3. rec record call
4. expect rec event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")

rec.stop()
rec.start()
rec.record_call("fn", nil, [], CallType.Direct)

expect rec.event_count() == 1
```

</details>

#### should clear all events

1. rec record call
2. rec record call
3. rec clear
4. expect rec event count
5. expect rec get classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. nil, Some
2. expect event format call


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect event format call


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Some
2. expect event get caller participant
3. expect event get callee participant


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Some
2. expect event format return


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect event format return


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
