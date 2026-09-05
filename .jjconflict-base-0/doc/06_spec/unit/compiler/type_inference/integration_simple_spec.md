# Integration Simple Specification

> Tests covering Type Inference CLI Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration Simple Specification

## Scenarios

### Type Inference CLI Integration

#### type checks a simple function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- run bin/simple run on a well-typed fixture, assert program result
   - Expected: result.2 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("run bin/simple run on a well-typed fixture, assert program result")
val result = process_run("bin/simple", ["run", "test/fixtures/type_inference/good_infer.spl"])
expect(result.2).to_equal(5)
```

</details>

#### detects type errors

- run bin/simple run on an ill-typed fixture, assert rejection
   - Expected: result.1 contains `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("run bin/simple run on an ill-typed fixture, assert rejection")
val result = process_run("bin/simple", ["run", "test/fixtures/type_inference/bad_type.spl"])
expect(result.2).to_not_equal(0)
expect(result.1.contains("error")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/type_inference/integration_simple_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Type Inference CLI Integration.
- Type Inference CLI Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3071bb856d85c587d78b465765f0ce061a1db990442d6b421d54033084fa1dba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3071bb856d85c587d78b465765f0ce061a1db990442d6b421d54033084fa1dba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3071bb856d85c587d78b465765f0ce061a1db990442d6b421d54033084fa1dba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/compiler/type_inference/integration_simple_spec.spl
mirror: doc/06_spec/unit/compiler/type_inference/integration_simple_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/type_inference/integration_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/type_inference/integration_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/type_inference/integration_simple_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/compiler/type_inference/integration_simple_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/type_inference/integration_simple_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'type checks a simple function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type_inference/integration_simple_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects type errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
