# Class Gen Specification

> 1. rec record call

<!-- sdn-diagram:id=class_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=class_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

class_gen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=class_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class Gen Specification

## Scenarios

### ClassDiagramGenerator

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
rec.record_call("method", Some("MyClass"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("```mermaid") == true
expect output.contains("classDiagram") == true
expect output.contains("```") == true
```

</details>

#### Class extraction

#### should extract class from method call

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("doWork", Some("UserService"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("class UserService") == true
```

</details>

#### should extract multiple classes

1. rec record call
2. rec record call
3. rec record call
4. expect output contains
5. expect output contains
6. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("methodA", Some("ClassA"), [], CallType.Method)
rec.record_call("methodB", Some("ClassB"), [], CallType.Method)
rec.record_call("methodC", Some("ClassC"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("class ClassA") == true
expect output.contains("class ClassB") == true
expect output.contains("class ClassC") == true
```

</details>

#### should not duplicate classes

1. rec record call
2. rec record call
3. rec record call


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("method1", Some("Service"), [], CallType.Method)
rec.record_call("method2", Some("Service"), [], CallType.Method)
rec.record_call("method3", Some("Service"), [], CallType.Method)

val output = to_mermaid_class(rec)

# Should only have one class declaration
val count = output.split("class Service").len() - 1
expect count == 1
```

</details>

#### should ignore non-method calls

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("standalone_fn", nil, [], CallType.Direct)

val output = to_mermaid_class(rec)

# Should not have any class declarations for function calls
expect output.contains("class standalone_fn") == false
```

</details>

#### Method extraction

#### should list methods in class

1. rec record call
2. rec record call
3. expect output contains
4. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("getUser", Some("UserService"), [], CallType.Method)
rec.record_call("saveUser", Some("UserService"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("getUser()") == true
expect output.contains("saveUser()") == true
```

</details>

#### should show public visibility

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("publicMethod", Some("MyClass"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("+publicMethod()") == true
```

</details>

#### Relationship extraction

#### should detect uses relationship

1. rec record call
2. rec record call
3. expect output contains
4. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
# ClassA calls ClassB
rec.record_call("methodA", Some("ClassA"), [], CallType.Method)
rec.record_call("methodB", Some("ClassB"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("ClassA --> ClassB") == true
expect output.contains("uses") == true
```

</details>

#### should not create self-relationship

1. rec record call
2. rec record call
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("method1", Some("Same"), [], CallType.Method)
rec.record_call("method2", Some("Same"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("Same --> Same") == false
```

</details>

#### should not duplicate relationships

1. rec record call
2. rec record call
3. rec record return
4. rec record call


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("a", Some("ClassA"), [], CallType.Method)
rec.record_call("b1", Some("ClassB"), [], CallType.Method)
rec.record_return(nil)
rec.record_call("b2", Some("ClassB"), [], CallType.Method)

val output = to_mermaid_class(rec)

# Should only have one relationship declaration
val count = output.split("ClassA --> ClassB").len() - 1
expect count == 1
```

</details>

#### Filtering

#### should apply include filter

1. rec record call
2. rec record call
3.  with class diagram
4.  with include
5. expect output contains
6. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("m", Some("UserService"), [], CallType.Method)
rec.record_call("m", Some("InternalHelper"), [], CallType.Method)

val config = DiagramConfig.new()
    .with_class_diagram()
    .with_include("*Service")

val output = generate_class_diagram(rec, config)

expect output.contains("UserService") == true
expect output.contains("InternalHelper") == false
```

</details>

#### should apply exclude filter

1. rec record call
2. rec record call
3.  with class diagram
4.  with exclude
5. expect output contains
6. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("m", Some("UserService"), [], CallType.Method)
rec.record_call("m", Some("DebugHelper"), [], CallType.Method)

val config = DiagramConfig.new()
    .with_class_diagram()
    .with_exclude("*Helper,*Debug*")

val output = generate_class_diagram(rec, config)

expect output.contains("UserService") == true
expect output.contains("DebugHelper") == false
```

</details>

### ClassInfo

#### Method tracking

#### should track unique methods

1. rec record call
2. rec record call
3. rec record call
4. expect output contains
5. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("method1", Some("Class"), [], CallType.Method)
rec.record_call("method1", Some("Class"), [], CallType.Method)
rec.record_call("method2", Some("Class"), [], CallType.Method)

val output = to_mermaid_class(rec)

# Should have both methods listed once each
expect output.contains("method1()") == true
expect output.contains("method2()") == true
```

</details>

### RelationType

#### Arrow formatting

#### should use arrow for uses relationship

1. rec record call
2. rec record call
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.record_call("caller_method", Some("Caller"), [], CallType.Method)
rec.record_call("callee_method", Some("Callee"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("-->") == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/diagram/class_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ClassDiagramGenerator
- ClassInfo
- RelationType

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
