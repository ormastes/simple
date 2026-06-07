# Arch Gen Specification

> 1. rec mark architectural

<!-- sdn-diagram:id=arch_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arch_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arch_gen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arch_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arch Gen Specification

## Scenarios

### ArchDiagramGenerator

#### Basic structure

#### should generate mermaid flowchart header

1. rec mark architectural
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
rec.mark_architectural("UserService")
rec.record_call("method", Some("UserService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("```mermaid") == true
expect output.contains("flowchart TD") == true
expect output.contains("```") == true
```

</details>

#### Architectural entity detection

#### should include @architectural tagged entities

1. rec mark architectural
2. rec mark architectural
3. rec record call
4. rec record call
5. expect output contains
6. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("UserService")
rec.mark_architectural("AuthService")
rec.record_call("m", Some("UserService"), [], CallType.Method)
rec.record_call("m", Some("AuthService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("UserService") == true
expect output.contains("AuthService") == true
```

</details>

#### should exclude non-architectural entities

1. rec mark architectural
2. rec record call
3. rec record call
4. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("Service")
rec.record_call("m", Some("Service"), [], CallType.Method)
rec.record_call("m", Some("HelperClass"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("Service") == true
# HelperClass is not marked architectural and not a package
# So it should be excluded (unless it matches package patterns)
```

</details>

#### should treat packages as architectural by default

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
# Qualified names with dots are treated as packages
rec.record_call("method", Some("app.services.UserService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("app") == true
```

</details>

#### should treat module paths as architectural

1. rec record call
2. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
# Double-colon paths (Rust style) are treated as packages
rec.record_call("method", Some("crate::services::UserService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("crate") == true
```

</details>

#### Package grouping

#### should group entities by package in subgraphs

1. rec mark architectural
2. rec mark architectural
3. rec record call
4. rec record call
5. expect output contains
6. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("app.services.UserService")
rec.mark_architectural("app.services.AuthService")
rec.record_call("m", Some("app.services.UserService"), [], CallType.Method)
rec.record_call("m", Some("app.services.AuthService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("subgraph") == true
expect output.contains("app") == true
```

</details>

#### should handle standalone entities without subgraph

1. rec mark architectural
2. rec record call
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("StandaloneService")
rec.record_call("m", Some("StandaloneService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("StandaloneService") == true
```

</details>

#### Dependency extraction

#### should show dependencies between architectural entities

1. rec mark architectural
2. rec mark architectural
3. rec record call
4. rec record call
5. expect output contains
6. expect output contains
7. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("Controller")
rec.mark_architectural("Service")

rec.record_call("handleRequest", Some("Controller"), [], CallType.Method)
rec.record_call("processData", Some("Service"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("Controller") == true
expect output.contains("Service") == true
expect output.contains("-->") == true
```

</details>

#### should not show dependencies to non-architectural entities

1. rec mark architectural
2. rec record call
3. rec record call
4. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("Service")

rec.record_call("method", Some("Service"), [], CallType.Method)
rec.record_call("helper", Some("InternalHelper"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("Service") == true
# Dependency to InternalHelper should not be shown
```

</details>

#### should track package-level dependencies

1. rec mark architectural
2. rec mark architectural
3. rec record call
4. rec record call
5. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("app.controllers.UserController")
rec.mark_architectural("app.services.UserService")

rec.record_call("m", Some("app.controllers.UserController"), [], CallType.Method)
rec.record_call("m", Some("app.services.UserService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

# Should show package-level dependency
expect output.contains("app") == true
```

</details>

#### should not create self-dependencies

1. rec mark architectural
2. rec record call
3. rec record call
4. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("Service")

rec.record_call("method1", Some("Service"), [], CallType.Method)
rec.record_call("method2", Some("Service"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("Service --> Service") == false
```

</details>

#### ID sanitization

#### should sanitize special characters in IDs

1. rec mark architectural
2. rec record call
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("app.services.UserService")
rec.record_call("m", Some("app.services.UserService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

# Dots should be replaced with underscores in IDs
expect output.contains("app_services_UserService") == true
```

</details>

#### Filtering

#### should apply include filter to architectural entities

1. rec mark architectural
2. rec mark architectural
3. rec record call
4. rec record call
5.  with architecture
6.  with include
7. expect output contains
8. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("UserService")
rec.mark_architectural("InternalService")

rec.record_call("m", Some("UserService"), [], CallType.Method)
rec.record_call("m", Some("InternalService"), [], CallType.Method)

val config = DiagramConfig.new()
    .with_architecture()
    .with_include("User*")

val output = generate_arch_diagram(rec, config)

expect output.contains("UserService") == true
expect output.contains("InternalService") == false
```

</details>

#### should apply exclude filter

1. rec mark architectural
2. rec mark architectural
3. rec record call
4. rec record call
5.  with architecture
6.  with exclude
7. expect output contains
8. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("UserService")
rec.mark_architectural("DebugService")

rec.record_call("m", Some("UserService"), [], CallType.Method)
rec.record_call("m", Some("DebugService"), [], CallType.Method)

val config = DiagramConfig.new()
    .with_architecture()
    .with_exclude("Debug*")

val output = generate_arch_diagram(rec, config)

expect output.contains("UserService") == true
expect output.contains("DebugService") == false
```

</details>

### ArchEntity

#### Package detection

#### should detect package from dot notation

1. rec mark architectural
2. rec record call
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("app.services.User")
rec.record_call("m", Some("app.services.User"), [], CallType.Method)

val output = to_mermaid_arch(rec)
expect output.contains("app") == true
```

</details>

#### should detect package from double-colon notation

1. rec mark architectural
2. rec record call
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("crate::module::Service")
rec.record_call("m", Some("crate::module::Service"), [], CallType.Method)

val output = to_mermaid_arch(rec)
expect output.contains("crate") == true
```

</details>

### ArchLayer

#### Layer classification

#### should handle unknown layer by default

1. rec mark architectural
2. rec record call
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = CallEventRecorder.new("test")
rec.mark_architectural("SomeService")
rec.record_call("m", Some("SomeService"), [], CallType.Method)

# Entities start with Unknown layer
val output = to_mermaid_arch(rec)
expect output.contains("SomeService") == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/diagram/arch_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ArchDiagramGenerator
- ArchEntity
- ArchLayer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
