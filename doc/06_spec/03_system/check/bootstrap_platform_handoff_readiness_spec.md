# Bootstrap platform handoff readiness

> Exercises the checker self-test and its default blocked report. This lane

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap platform handoff readiness

Exercises the checker self-test and its default blocked report. This lane

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/bootstrap_platform_handoff_readiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the checker self-test and its default blocked report. This lane
proves checker wiring and the claim boundary only; it does not execute a
platform bootstrap or provide platform acceptance evidence.

## Scenarios

### Bootstrap platform handoff readiness

### BPHR-001/BPHR-002: checker self-test claim boundary

#### should execute the checker self-test without a platform PASS claim

- should execute the checker self-test without a platform PASS claim
- Run the bootstrap platform handoff checker self-test
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the checker self-test without a platform PASS claim")
step("Run the bootstrap platform handoff checker self-test")
val readiness = step_bootstrap_platform_handoff_readiness()
expect(readiness).to_contain("BPHR-001")
expect(readiness).to_contain("BPHR-002")
val (stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["-c", "sh scripts/check/check-bootstrap-platform-handoff-readiness.shs --self-test"]
)
expect(code).to_equal(0)
expect(stdout).to_contain("bootstrap_handoff_self_test=pass")
expect(stdout).to_contain("platform_acceptance_claimed=false")
```

</details>

### BPHR-003/BPHR-004: default blocked handoff

#### should report the default handoff as blocked and not platform PASS

- should report the default handoff as blocked and not platform PASS
- Run the default bootstrap platform handoff readiness check
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report the default handoff as blocked and not platform PASS")
step("Run the default bootstrap platform handoff readiness check")
val readiness = step_bootstrap_platform_handoff_readiness()
expect(readiness).to_contain("BPHR-003")
expect(readiness).to_contain("BPHR-004")
val (stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["-c", "sh scripts/check/check-bootstrap-platform-handoff-readiness.shs"]
)
expect(code).to_equal(1)
expect(stdout).to_contain("bootstrap_handoff_readiness_status=blocked")
expect(stdout).to_contain("bootstrap_handoff_readiness_reason=stage3_candidate:")
expect(stdout).to_contain("bootstrap_handoff_remaining_gate_count=")
expect(stdout).to_contain("platform_acceptance_claimed=false")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da129bba3a9630e8c70bf2d4c948d97d93d72d65188ccb61a2a3bf45808b76a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da129bba3a9630e8c70bf2d4c948d97d93d72d65188ccb61a2a3bf45808b76a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da129bba3a9630e8c70bf2d4c948d97d93d72d65188ccb61a2a3bf45808b76a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/bootstrap_platform_handoff_readiness_spec.spl
mirror: doc/06_spec/03_system/check/bootstrap_platform_handoff_readiness_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/bootstrap_platform_handoff_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/bootstrap_platform_handoff_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/bootstrap_platform_handoff_readiness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/bootstrap_platform_handoff_readiness_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the checker self-test without a platform PASS claim' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/bootstrap_platform_handoff_readiness_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute the checker self-test without a platform PASS claim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/bootstrap_platform_handoff_readiness_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report the default handoff as blocked and not platform PASS' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/bootstrap_platform_handoff_readiness_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report the default handoff as blocked and not platform PASS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
