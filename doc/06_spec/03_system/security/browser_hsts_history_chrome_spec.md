# HSTS-safe hosted history chrome

> Back and Forward bind the HSTS-upgraded traversal ledger to the SBR2 command

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HSTS-safe hosted history chrome

Back and Forward bind the HSTS-upgraded traversal ledger to the SBR2 command

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_hsts_history_chrome_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Back and Forward bind the HSTS-upgraded traversal ledger to the SBR2 command
capability. The parent publishes that off-side ledger only after validating
the final renderer proposal; Stop, replacement, and rejection preserve the
previously committed ledger.

## Scenarios

### Hosted HSTS history chrome

#### should bind upgraded traversal history to hosted chrome

- should bind upgraded traversal history to hosted chrome
   - Protocol capture: after_step
- Commit HTTP history before learning HSTS
   - Protocol capture: after_step
- Learn HSTS and activate Back through hosted chrome
   - Protocol capture: after_step
- Commit one upgraded traversal ledger atomically
   - Protocol capture: after_step
- Preserve Stop retry and Forward projections
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind upgraded traversal history to hosted chrome")
step("Commit HTTP history before learning HSTS")
var fixture = setup_hsts_history_chrome_fixture()

step("Learn HSTS and activate Back through hosted chrome")
activate_back_through_hosted_chrome(fixture)

step("Commit one upgraded traversal ledger atomically")
check_upgraded_history_commit(fixture)

step("Preserve Stop retry and Forward projections")
check_stop_retry_forward_projection(fixture)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `e6f66f97088914f9232440c8a415d0b6c605299343ec5cdb8692db24921d1c45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e6f66f97088914f9232440c8a415d0b6c605299343ec5cdb8692db24921d1c45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e6f66f97088914f9232440c8a415d0b6c605299343ec5cdb8692db24921d1c45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/security/browser_hsts_history_chrome_spec.spl
mirror: doc/06_spec/03_system/security/browser_hsts_history_chrome_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/security/browser_hsts_history_chrome_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_hsts_history_chrome_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_hsts_history_chrome_spec.spl:332:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind upgraded traversal history to hosted chrome' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_hsts_history_chrome_spec.spl:332:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind upgraded traversal history to hosted chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
