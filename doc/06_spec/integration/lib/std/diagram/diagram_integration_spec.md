# Diagram Integration Specification

> Tests covering Diagram Integration, Diagram Tracing API.

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

- should generate diagram from method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should generate diagram from method calls")
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

- should include timing and return values


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should include timing and return values")
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

- should extract classes from calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should extract classes from calls")
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

- should show relationships


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should show relationships")
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

- should show only architectural entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should show only architectural entities")
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

- should treat packages as architectural by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should treat packages as architectural by default")
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

- should apply include filter across diagrams


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should apply include filter across diagrams")
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

- should apply exclude filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should apply exclude filter")
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

- should generate all diagrams from same recording


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should generate all diagrams from same recording")
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

- should record traced calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should record traced calls")
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

- should track architectural entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should track architectural entities")
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
| Source | `test/integration/lib/std/diagram/diagram_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Diagram Integration, Diagram Tracing API.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81b807306ca0b5d51a2d3ad41f25737b5737ab85701c589aaab507587baa97e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81b807306ca0b5d51a2d3ad41f25737b5737ab85701c589aaab507587baa97e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81b807306ca0b5d51a2d3ad41f25737b5737ab85701c589aaab507587baa97e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/lib/std/diagram/diagram_integration_spec.spl
mirror: doc/06_spec/integration/lib/std/diagram/diagram_integration_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/std/diagram/diagram_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/std/diagram/diagram_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/std/diagram/diagram_integration_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate diagram from method calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/lib/std/diagram/diagram_integration_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should generate diagram from method calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/diagram/diagram_integration_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include timing and return values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/lib/std/diagram/diagram_integration_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include timing and return values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/diagram/diagram_integration_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract classes from calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/lib/std/diagram/diagram_integration_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract classes from calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/diagram/diagram_integration_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should show relationships' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/lib/std/diagram/diagram_integration_spec.spl:102:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should show only architectural entities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/lib/std/diagram/diagram_integration_spec.spl:121:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should treat packages as architectural by default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
