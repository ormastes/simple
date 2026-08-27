# Pure-Simple Bootstrap Stage Sanity

> Prove that each retained pure-Simple bootstrap stage starts, rejects unsupported `run` dispatch, compiles the canonical tiny redeploy fixture with stub fallback disabled, and runs it.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure-Simple Bootstrap Stage Sanity

Prove that each retained pure-Simple bootstrap stage starts, rejects unsupported `run` dispatch, compiles the canonical tiny redeploy fixture with stub fallback disabled, and runs it.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/02_requirements/app/build/bootstrap.md |
| Plan | doc/03_plan/sys_test/pure_simple_stage_sanity.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Prove that each retained pure-Simple bootstrap stage starts, rejects unsupported
`run` dispatch, compiles the canonical tiny redeploy fixture with stub
fallback disabled, and runs it.

## Examples

Stage 2 and Stage 3 each compile `p2_add.spl`; the produced native program
must exit successfully and print exactly `5`.

## Scenarios

### Pure-Simple Bootstrap Stage Sanity

### REQ-BOOT-STAGE-001: every retained pure-Simple stage is executable

#### should prove Stage 2 can compile and run a native fixture

- should prove Stage 2 can compile and run a native fixture
- Start Stage 2 and require its bootstrap version
- Reject unsupported run without native-build misrouting
- Strictly compile the canonical tiny fixture
- Run the Stage 2-produced fixture and require output 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-BOOT-STAGE-001 REQ-SSPEC-SYSTEM
step("should prove Stage 2 can compile and run a native fixture")
step("Start Stage 2 and require its bootstrap version")
step("Reject unsupported run without native-build misrouting")
step("Strictly compile the canonical tiny fixture")
step("Run the Stage 2-produced fixture and require output 5")
expect_stage_sane("stage2")
```

</details>

#### should prove Stage 3 can compile and run a native fixture

- should prove Stage 3 can compile and run a native fixture
- Start Stage 3 and require its bootstrap version
- Reject unsupported run without native-build misrouting
- Strictly compile the canonical tiny fixture
- Run the Stage 3-produced fixture and require output 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prove Stage 3 can compile and run a native fixture")
step("Start Stage 3 and require its bootstrap version")
step("Reject unsupported run without native-build misrouting")
step("Strictly compile the canonical tiny fixture")
step("Run the Stage 3-produced fixture and require output 5")
expect_stage_sane("stage3")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/app/build/bootstrap.md`
- **Plan:** `doc/03_plan/sys_test/pure_simple_stage_sanity.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-BOOT-STAGE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33f405b9ec688b7c8ae386bd6aa1cd171d02b98242469dccabaf81ea676d8ec8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33f405b9ec688b7c8ae386bd6aa1cd171d02b98242469dccabaf81ea676d8ec8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33f405b9ec688b7c8ae386bd6aa1cd171d02b98242469dccabaf81ea676d8ec8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/pure_simple_stage_sanity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/pure_simple_stage_sanity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/pure_simple_stage_sanity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prove Stage 2 can compile and run a native fixture' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prove Stage 2 can compile and run a native fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl:117:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prove Stage 3 can compile and run a native fixture' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prove Stage 3 can compile and run a native fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
