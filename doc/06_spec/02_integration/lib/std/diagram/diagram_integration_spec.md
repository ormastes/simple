# Diagram Integration Specification

> 1. rec record call

<!-- sdn-diagram:id=diagram_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagram_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagram_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagram_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagram Integration Specification

## Scenarios

### Diagram Integration

#### Sequence diagram generation

#### should generate diagram from method calls

1. rec record call
2. rec record call
3. rec record return
4. rec record return
5. expect output contains
6. expect output contains
7. expect output contains
8. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("auth_test")

rec.record_call("authenticate", Some("UserService"), ["admin", "***"], CallType.Method)
rec.record_call("validate_credentials", Some("UserService"), ["admin"], CallType.Method)
rec.record_return(Some("true"))
rec.record_return(Some("true"))

val config = DiagramConfig.new().with_sequence()
val output = generate_sequence(rec, config)

expect output.contains("sequenceDiagram") == true
expect output.contains("UserService") == true
expect output.contains("authenticate") == true
expect output.contains("validate_credentials") == true
```

</details>

#### should include timing and return values

1. rec record call
2. rec record return
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("timing_test")

rec.record_call("process", Some("Handler"), ["data"], CallType.Method)
rec.record_return(Some("Result(42)"))

val config = DiagramConfig.new().with_sequence()
val output = generate_sequence(rec, config)

expect output.contains("Result(42)") == true
```

</details>

#### Class diagram generation

#### should extract classes from calls

1. rec record call
2. rec record call
3. rec record call
4. expect output contains
5. expect output contains
6. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("class_test")

rec.record_call("methodA", Some("ClassA"), [], CallType.Method)
rec.record_call("methodB", Some("ClassB"), [], CallType.Method)
rec.record_call("methodC", Some("ClassA"), [], CallType.Method)

val config = DiagramConfig.new().with_class_diagram()
val output = generate_class_diagram(rec, config)

expect output.contains("classDiagram") == true
expect output.contains("class ClassA") == true
expect output.contains("class ClassB") == true
```

</details>

#### should show relationships

1. rec record call
2. rec record call
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("rel_test")

rec.record_call("handleRequest", Some("Controller"), [], CallType.Method)
rec.record_call("process", Some("Service"), [], CallType.Method)

val config = DiagramConfig.new().with_class_diagram()
val output = generate_class_diagram(rec, config)

expect output.contains("Controller --> Service") == true
```

</details>

#### Architecture diagram generation

#### should show only architectural entities

1. rec mark architectural
2. rec mark architectural
3. rec record call
4. rec record call
5. rec record call
6. expect output contains
7. expect output contains
8. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("arch_test")

rec.mark_architectural("UserService")
rec.mark_architectural("AuthService")

rec.record_call("method", Some("UserService"), [], CallType.Method)
rec.record_call("method", Some("Helper"), [], CallType.Method)
rec.record_call("method", Some("AuthService"), [], CallType.Method)

val config = DiagramConfig.new().with_architecture()
val output = generate_arch_diagram(rec, config)

expect output.contains("flowchart TD") == true
expect output.contains("UserService") == true
expect output.contains("AuthService") == true
```

</details>

#### should treat packages as architectural by default

1. rec record call
2. rec record call
3. expect output contains
4. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("pkg_test")

rec.record_call("method", Some("app.services.UserService"), [], CallType.Method)
rec.record_call("method", Some("app.repos.UserRepo"), [], CallType.Method)

val config = DiagramConfig.new().with_architecture()
val output = generate_arch_diagram(rec, config)

expect output.contains("subgraph") == true
expect output.contains("app") == true
```

</details>

#### Filtering

#### should apply include filter across diagrams

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

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("filter_test")

rec.record_call("m", Some("UserService"), [], CallType.Method)
rec.record_call("m", Some("DebugHelper"), [], CallType.Method)
rec.record_call("m", Some("AuthService"), [], CallType.Method)

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

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("exclude_test")

rec.record_call("m", Some("UserService"), [], CallType.Method)
rec.record_call("m", Some("InternalHelper"), [], CallType.Method)

val config = DiagramConfig.new()
    .with_sequence()
    .with_exclude("*Helper,*Internal*")

val output = generate_sequence(rec, config)

expect output.contains("UserService") == true
expect output.contains("InternalHelper") == false
```

</details>

#### All diagram types

#### should generate all diagrams from same recording

1. rec mark architectural
2. rec mark architectural
3. rec record call
4. rec record call
5. rec record return
6. rec record return
7. expect seq contains
8. expect cls contains
9. expect arch contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("all_test")

rec.mark_architectural("Controller")
rec.mark_architectural("Service")

rec.record_call("handle", Some("Controller"), [], CallType.Method)
rec.record_call("process", Some("Service"), ["data"], CallType.Method)
rec.record_return(Some("result"))
rec.record_return(Some("response"))

val config = DiagramConfig.new().with_all()

# Sequence diagram
val seq = generate_sequence(rec, config)
expect seq.contains("sequenceDiagram") == true

# Class diagram
val cls = generate_class_diagram(rec, config)
expect cls.contains("classDiagram") == true

# Architecture diagram
val arch = generate_arch_diagram(rec, config)
expect arch.contains("flowchart TD") == true
```

</details>

### Diagram Tracing API

#### Manual tracing

#### should record traced calls

1. diagram set recorder
2. trace method
3. trace return
4. expect events len
5. expect events[0] callee class == Some
6. diagram clear recorder


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("trace_test")
diagram.set_recorder(rec)

trace_method("MyClass", "myMethod", ["arg1", "arg2"])
trace_return(Some("result"))

val events = rec.get_events()
expect events.len() == 2
expect events[0].callee == "myMethod"
expect events[0].callee_class == Some("MyClass")

diagram.clear_recorder()
```

</details>

#### should track architectural entities

1. diagram set recorder
2. mark architectural
3. mark architectural
4. expect rec is architectural
5. expect rec is architectural
6. expect rec is architectural
7. diagram clear recorder


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("arch_trace_test")
diagram.set_recorder(rec)

mark_architectural("CoreService")
mark_architectural("Repository")

expect rec.is_architectural("CoreService") == true
expect rec.is_architectural("Repository") == true
expect rec.is_architectural("Helper") == false

diagram.clear_recorder()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/diagram/diagram_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Diagram Integration
- Diagram Tracing API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
