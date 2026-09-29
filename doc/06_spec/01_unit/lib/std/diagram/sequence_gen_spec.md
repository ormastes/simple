# Sequence Gen Specification

> Tests covering SequenceGenerator, Participant.

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

- should generate mermaid header


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should generate mermaid header")
val rec = CallEventRecorder.new("test")
rec.record_call("target", nil, [], CallType.Direct)

val output = to_mermaid_sequence(rec)

expect output.contains("```mermaid") == true
expect output.contains("sequenceDiagram") == true
expect output.contains("```") == true
```

</details>

#### should include autonumber

- should include autonumber


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should include autonumber")
val rec = CallEventRecorder.new("test")
rec.record_call("target", nil, [], CallType.Direct)

val output = to_mermaid_sequence(rec)

expect output.contains("autonumber") == true
```

</details>

#### Participant generation

#### should declare participants

- should declare participants


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should declare participants")
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

- should create aliases for long names


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should create aliases for long names")
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

- should generate call arrow


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should generate call arrow")
val rec = CallEventRecorder.new("test")
rec.record_call("doWork", Some("Service"), [], CallType.Method)

val output = to_mermaid_sequence(rec)

expect output.contains("->>") == true
expect output.contains("doWork") == true
```

</details>

#### should include arguments in call

- should include arguments in call


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should include arguments in call")
val rec = CallEventRecorder.new("test")
rec.record_call("process", Some("Handler"), ["data", "42"], CallType.Method)

val config = DiagramConfig.new().with_sequence()
val output = generate_sequence(rec, config)

expect output.contains("process(data, 42)") == true
```

</details>

#### should activate callee on call

- should activate callee on call


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should activate callee on call")
val rec = CallEventRecorder.new("test")
rec.record_call("target", Some("Target"), [], CallType.Method)

val output = to_mermaid_sequence(rec)

expect output.contains("activate") == true
```

</details>

#### Return arrows

#### should generate return arrow

- should generate return arrow


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should generate return arrow")
val rec = CallEventRecorder.new("test")
rec.record_call("getValue", Some("Store"), [], CallType.Method)
rec.record_return(Some("42"))

val output = to_mermaid_sequence(rec)

expect output.contains("-->>") == true
```

</details>

#### should include return value

- should include return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should include return value")
val rec = CallEventRecorder.new("test")
rec.record_call("calculate", Some("Calculator"), [], CallType.Method)
rec.record_return(Some("Result(100)"))

val config = DiagramConfig.new().with_sequence()
val output = generate_sequence(rec, config)

expect output.contains("Result(100)") == true
```

</details>

#### should deactivate on return

- should deactivate on return


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should deactivate on return")
val rec = CallEventRecorder.new("test")
rec.record_call("target", Some("Target"), [], CallType.Method)
rec.record_return(nil)

val output = to_mermaid_sequence(rec)

expect output.contains("deactivate") == true
```

</details>

#### Nested calls

#### should handle nested call sequence

- should handle nested call sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should handle nested call sequence")
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

- should omit timing when disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should omit timing when disabled")
val rec = CallEventRecorder.new("test")
rec.record_call("fn", nil, [], CallType.Direct)

val config = DiagramConfig.new().with_sequence().without_timing()
val output = generate_sequence(rec, config)

expect output.contains("Note over") == false
```

</details>

#### should omit args when disabled

- should omit args when disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should omit args when disabled")
val rec = CallEventRecorder.new("test")
rec.record_call("fn", nil, ["arg1", "arg2"], CallType.Direct)

val config = DiagramConfig.new().with_sequence().without_args()
val output = generate_sequence(rec, config)

expect output.contains("arg1") == false
expect output.contains("arg2") == false
```

</details>

#### should respect max events limit

- should respect max events limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should respect max events limit")
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

- should apply include filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should apply include filter")
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

- should apply exclude filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should apply exclude filter")
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

- should create short alias for long name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should create short alias for long name")
val rec = CallEventRecorder.new("test")
rec.record_call("m", Some("VeryLongServiceName"), [], CallType.Method)

val output = to_mermaid_sequence(rec)
# Should have abbreviated alias
expect output.contains("participant") == true
```

</details>

#### should use name as alias for short names

- should use name as alias for short names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should use name as alias for short names")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SequenceGenerator, Participant.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0efdf26746370cd5b05c807b5b90635540b30005adcf3827b8d4e511ca9a51bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0efdf26746370cd5b05c807b5b90635540b30005adcf3827b8d4e511ca9a51bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0efdf26746370cd5b05c807b5b90635540b30005adcf3827b8d4e511ca9a51bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/std/diagram/sequence_gen_spec.spl
mirror: doc/06_spec/01_unit/lib/std/diagram/sequence_gen_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/diagram/sequence_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/diagram/sequence_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate mermaid header' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should generate mermaid header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include autonumber' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include autonumber' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should declare participants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should declare participants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create aliases for long names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate call arrow' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/diagram/sequence_gen_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include arguments in call' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
