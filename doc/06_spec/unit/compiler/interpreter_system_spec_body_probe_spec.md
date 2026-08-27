# Interpreter System Spec Body Probe Specification

> Tests covering interpreter it-body execution probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter System Spec Body Probe Specification

## Scenarios

### interpreter it-body execution probe

#### arithmetic inside it body

#### evaluates expressions inside the block

- evaluates expressions inside the block
   - Expected: sum equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates expressions inside the block")
val sum = 2 + 3
expect(sum).to_equal(5)
```

</details>

#### evaluates boolean comparisons

- evaluates boolean comparisons
   - Expected: truthy is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates boolean comparisons")
val truthy = 10 > 3
expect(truthy).to_equal(true)
```

</details>

#### local variable bindings inside it body

#### binds and reads a local variable

- binds and reads a local variable
   - Expected: name equals `agent_x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds and reads a local variable")
val name = "agent_x"
expect(name).to_equal("agent_x")
```

</details>

#### supports multi-step computation

- supports multi-step computation
   - Expected: product equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multi-step computation")
val a = 7
val b = 6
val product = a * b
expect(product).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/interpreter_system_spec_body_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter it-body execution probe.
- interpreter it-body execution probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `8b66ecac55fd31a5b3ca772accc06256e990683a86f1c3094add1810b3d44389`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b66ecac55fd31a5b3ca772accc06256e990683a86f1c3094add1810b3d44389`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b66ecac55fd31a5b3ca772accc06256e990683a86f1c3094add1810b3d44389`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/interpreter_system_spec_body_probe_spec.spl
mirror: doc/06_spec/unit/compiler/interpreter_system_spec_body_probe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/interpreter_system_spec_body_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/interpreter_system_spec_body_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/interpreter_system_spec_body_probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/interpreter_system_spec_body_probe_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates expressions inside the block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter_system_spec_body_probe_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates boolean comparisons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter_system_spec_body_probe_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds and reads a local variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
