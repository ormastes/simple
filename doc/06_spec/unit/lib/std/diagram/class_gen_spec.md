# Class Gen Specification

> Tests covering ClassDiagramGenerator, ClassInfo, RelationType.

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

- should generate mermaid header


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should generate mermaid header")
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

- should extract class from method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should extract class from method call")
val rec = CallEventRecorder.new("test")
rec.record_call("doWork", Some("UserService"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("class UserService") == true
```

</details>

#### should extract multiple classes

- should extract multiple classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should extract multiple classes")
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

- should not duplicate classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not duplicate classes")
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

- should ignore non-method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should ignore non-method calls")
val rec = CallEventRecorder.new("test")
rec.record_call("standalone_fn", nil, [], CallType.Direct)

val output = to_mermaid_class(rec)

# Should not have any class declarations for function calls
expect output.contains("class standalone_fn") == false
```

</details>

#### Method extraction

#### should list methods in class

- should list methods in class


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should list methods in class")
val rec = CallEventRecorder.new("test")
rec.record_call("getUser", Some("UserService"), [], CallType.Method)
rec.record_call("saveUser", Some("UserService"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("getUser()") == true
expect output.contains("saveUser()") == true
```

</details>

#### should show public visibility

- should show public visibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should show public visibility")
val rec = CallEventRecorder.new("test")
rec.record_call("publicMethod", Some("MyClass"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("+publicMethod()") == true
```

</details>

#### Relationship extraction

#### should detect uses relationship

- should detect uses relationship


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should detect uses relationship")
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

- should not create self-relationship


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not create self-relationship")
val rec = CallEventRecorder.new("test")
rec.record_call("method1", Some("Same"), [], CallType.Method)
rec.record_call("method2", Some("Same"), [], CallType.Method)

val output = to_mermaid_class(rec)

expect output.contains("Same --> Same") == false
```

</details>

#### should not duplicate relationships

- should not duplicate relationships


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not duplicate relationships")
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

- should apply include filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should apply include filter")
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

- should apply exclude filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should apply exclude filter")
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

- should track unique methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should track unique methods")
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

- should use arrow for uses relationship


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should use arrow for uses relationship")
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
| Source | `test/unit/lib/std/diagram/class_gen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ClassDiagramGenerator, ClassInfo, RelationType.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee49617711f6f449caa3ced8dde109c90a3b22138726d7da52fe9ae85335ad07`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee49617711f6f449caa3ced8dde109c90a3b22138726d7da52fe9ae85335ad07`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee49617711f6f449caa3ced8dde109c90a3b22138726d7da52fe9ae85335ad07`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/std/diagram/class_gen_spec.spl
mirror: doc/06_spec/unit/lib/std/diagram/class_gen_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/diagram/class_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/diagram/class_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/diagram/class_gen_spec.spl:21:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate mermaid header' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/class_gen_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should generate mermaid header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/diagram/class_gen_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract class from method call' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/class_gen_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract class from method call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/diagram/class_gen_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract multiple classes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/class_gen_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract multiple classes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/diagram/class_gen_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not duplicate classes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/class_gen_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should ignore non-method calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/diagram/class_gen_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should list methods in class' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
