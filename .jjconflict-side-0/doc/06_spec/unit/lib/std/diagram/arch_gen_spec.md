# Arch Gen Specification

> Tests covering ArchDiagramGenerator, ArchEntity, ArchLayer.

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

- should generate mermaid flowchart header


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should generate mermaid flowchart header")
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

- should include @architectural tagged entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include @architectural tagged entities")
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

- should exclude non-architectural entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should exclude non-architectural entities")
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

- should treat packages as architectural by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should treat packages as architectural by default")
val rec = CallEventRecorder.new("test")
# Qualified names with dots are treated as packages
rec.record_call("method", Some("app.services.UserService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("app") == true
```

</details>

#### should treat module paths as architectural

- should treat module paths as architectural


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should treat module paths as architectural")
val rec = CallEventRecorder.new("test")
# Double-colon paths (Rust style) are treated as packages
rec.record_call("method", Some("crate::services::UserService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("crate") == true
```

</details>

#### Package grouping

#### should group entities by package in subgraphs

- should group entities by package in subgraphs


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should group entities by package in subgraphs")
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

- should handle standalone entities without subgraph


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle standalone entities without subgraph")
val rec = CallEventRecorder.new("test")
rec.mark_architectural("StandaloneService")
rec.record_call("m", Some("StandaloneService"), [], CallType.Method)

val output = to_mermaid_arch(rec)

expect output.contains("StandaloneService") == true
```

</details>

#### Dependency extraction

#### should show dependencies between architectural entities

- should show dependencies between architectural entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should show dependencies between architectural entities")
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

- should not show dependencies to non-architectural entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not show dependencies to non-architectural entities")
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

- should track package-level dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should track package-level dependencies")
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

- should not create self-dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not create self-dependencies")
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

- should sanitize special characters in IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should sanitize special characters in IDs")
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

- should apply include filter to architectural entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should apply include filter to architectural entities")
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

- should apply exclude filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should apply exclude filter")
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

- should detect package from dot notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should detect package from dot notation")
val rec = CallEventRecorder.new("test")
rec.mark_architectural("app.services.User")
rec.record_call("m", Some("app.services.User"), [], CallType.Method)

val output = to_mermaid_arch(rec)
expect output.contains("app") == true
```

</details>

#### should detect package from double-colon notation

- should detect package from double-colon notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should detect package from double-colon notation")
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

- should handle unknown layer by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle unknown layer by default")
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
| Source | `test/unit/lib/std/diagram/arch_gen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ArchDiagramGenerator, ArchEntity, ArchLayer.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `49fe4abf42c5c521297b80d512636bcd320b51902166ab0a65431f7899149023`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49fe4abf42c5c521297b80d512636bcd320b51902166ab0a65431f7899149023`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49fe4abf42c5c521297b80d512636bcd320b51902166ab0a65431f7899149023`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/std/diagram/arch_gen_spec.spl
mirror: doc/06_spec/unit/lib/std/diagram/arch_gen_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/diagram/arch_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/diagram/arch_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/diagram/arch_gen_spec.spl:21:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate mermaid flowchart header' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/arch_gen_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should generate mermaid flowchart header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/diagram/arch_gen_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include @architectural tagged entities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/arch_gen_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include @architectural tagged entities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/diagram/arch_gen_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exclude non-architectural entities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/arch_gen_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exclude non-architectural entities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/diagram/arch_gen_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should treat packages as architectural by default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/arch_gen_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should treat module paths as architectural' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/arch_gen_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should group entities by package in subgraphs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
