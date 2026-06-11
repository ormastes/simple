# Sequence Gen Specification

> 1. rec record call

<!-- sdn-diagram:id=sequence_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sequence_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sequence_gen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sequence_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sequence Gen Specification

## Scenarios

### SequenceGenerator

#### Basic structure

#### should generate mermaid header

1. rec record call
2. expect output contains
3. expect output contains
4. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("target", nil, [], CallType.Direct)

val output = to_mermaid_sequence(rec)

expect output.contains("```mermaid") == true
expect output.contains("sequenceDiagram") == true
expect output.contains("```") == true
```

</details>

#### should include autonumber

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("target", nil, [], CallType.Direct)

val output = to_mermaid_sequence(rec)

expect output.contains("autonumber") == true
```

</details>

#### Participant generation

#### should declare participants

1. rec record call
2. rec record call
3. expect output contains
4. expect output contains
5. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("methodA", Some("ClassA"), [], CallType.Method)
rec.record_call("methodB", Some("ClassB"), [], CallType.Method)

val output = to_mermaid_sequence(rec)

expect output.contains("participant") == true
expect output.contains("ClassA") == true
expect output.contains("ClassB") == true
```

</details>

#### should create aliases for long names

1. rec record call
2. expect output contains
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("method", Some("VeryLongClassName"), [], CallType.Method)

val config = DiagramConfig.new().with_sequence()
val output = generate_sequence(rec, config)

# Should have alias declaration
expect output.contains("participant") == true
expect output.contains("VeryLongClassName") == true
```

</details>

#### Call arrows

#### should generate call arrow

1. rec record call
2. expect output contains
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("doWork", Some("Service"), [], CallType.Method)

val output = to_mermaid_sequence(rec)

expect output.contains("->>") == true
expect output.contains("doWork") == true
```

</details>

#### should include arguments in call

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("process", Some("Handler"), ["data", "42"], CallType.Method)

val config = DiagramConfig.new().with_sequence()
val output = generate_sequence(rec, config)

expect output.contains("process(data, 42)") == true
```

</details>

#### should activate callee on call

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("target", Some("Target"), [], CallType.Method)

val output = to_mermaid_sequence(rec)

expect output.contains("activate") == true
```

</details>

#### Return arrows

#### should generate return arrow

1. rec record call
2. rec record return
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("getValue", Some("Store"), [], CallType.Method)
rec.record_return(Some("42"))

val output = to_mermaid_sequence(rec)

expect output.contains("-->>") == true
```

</details>

#### should include return value

1. rec record call
2. rec record return
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("calculate", Some("Calculator"), [], CallType.Method)
rec.record_return(Some("Result(100)"))

val config = DiagramConfig.new().with_sequence()
val output = generate_sequence(rec, config)

expect output.contains("Result(100)") == true
```

</details>

#### should deactivate on return

1. rec record call
2. rec record return
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("target", Some("Target"), [], CallType.Method)
rec.record_return(nil)

val output = to_mermaid_sequence(rec)

expect output.contains("deactivate") == true
```

</details>

#### Nested calls

#### should handle nested call sequence

1. rec record call
2. rec record call
3. rec record return
4. rec record call
5. rec record return
6. rec record return
7. expect output contains
8. expect output contains
9. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")

rec.record_call("handleRequest", Some("Controller"), [], CallType.Method)
rec.record_call("validateInput", Some("Validator"), ["input"], CallType.Method)
rec.record_return(Some("true"))
rec.record_call("processData", Some("Service"), ["data"], CallType.Method)
rec.record_return(Some("result"))
rec.record_return(Some("response"))

val output = to_mermaid_sequence(rec)

expect output.contains("Controller") == true
expect output.contains("Validator") == true
expect output.contains("Service") == true
```

</details>

#### Configuration options

#### should omit timing when disabled

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("fn", nil, [], CallType.Direct)

val config = DiagramConfig.new().with_sequence().without_timing()
val output = generate_sequence(rec, config)

expect output.contains("Note over") == false
```

</details>

#### should omit args when disabled

1. rec record call
2. expect output contains
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("fn", nil, ["arg1", "arg2"], CallType.Direct)

val config = DiagramConfig.new().with_sequence().without_args()
val output = generate_sequence(rec, config)

expect output.contains("arg1") == false
expect output.contains("arg2") == false
```

</details>

#### should respect max events limit

1. rec record call
2. expect output contains
3. expect output contains
4. expect output contains
5. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
for i in 0..10:
    rec.record_call("fn${i}", nil, [], CallType.Direct)

val config = DiagramConfig.new().with_sequence().with_max_events(3)
val output = generate_sequence(rec, config)

# Should only have first 3 events
expect output.contains("fn0") == true
expect output.contains("fn1") == true
expect output.contains("fn2") == true
expect output.contains("fn9") == false
```

</details>

#### Filtering

#### should apply include filter

1. rec record call
2. rec record call
3. rec record call
4.  with sequence
5.  with include
6. expect output contains
7. expect output contains
8. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("method", Some("UserService"), [], CallType.Method)
rec.record_call("method", Some("DebugHelper"), [], CallType.Method)
rec.record_call("method", Some("AuthService"), [], CallType.Method)

val config = DiagramConfig.new()
    .with_sequence()
    .with_include("*Service")

val output = generate_sequence(rec, config)

expect output.contains("UserService") == true
expect output.contains("AuthService") == true
expect output.contains("DebugHelper") == false
```

</details>

#### should apply exclude filter

1. rec record call
2. rec record call
3.  with sequence
4.  with exclude
5. expect output contains
6. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("method", Some("UserService"), [], CallType.Method)
rec.record_call("method", Some("InternalHelper"), [], CallType.Method)

val config = DiagramConfig.new()
    .with_sequence()
    .with_exclude("*Helper,*Internal*")

val output = generate_sequence(rec, config)

expect output.contains("UserService") == true
expect output.contains("InternalHelper") == false
```

</details>

### Participant

#### Alias creation

#### should create short alias for long name

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("m", Some("VeryLongServiceName"), [], CallType.Method)

val output = to_mermaid_sequence(rec)
# Should have abbreviated alias
expect output.contains("participant") == true
```

</details>

#### should use name as alias for short names

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("m", Some("User"), [], CallType.Method)

val output = to_mermaid_sequence(rec)
expect output.contains("User") == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/diagram/sequence_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SequenceGenerator
- Participant

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
