# Bootstrap Reason Planner Source Specification

> Tests covering minimal bootstrap reason planner source contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Reason Planner Source Specification

## Scenarios

### minimal bootstrap reason planner source contract

#### uses the typed policy and canonical file facade

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the typed policy and canonical file facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the typed policy and canonical file facade")
val source = rt_file_read_text(
    "src/app/cli/bootstrap_reason_planner.spl") ?? ""
# Receipt schema moved v1 -> v2 (src/app/cli/bootstrap_reason_planner.spl:72-73);
# the invariant asserted here -- a versioned receipt header plus a
# producer tag -- is unchanged, only the version token moved.
expect(source).to_contain("simple-bootstrap-authorization-v2")
expect(source).to_contain("simple-build-planner-v2")
expect(source).to_contain("planner_reason_allowed")
expect(source).to_contain("fn planner_file_write")
expect(source).to_contain("bootstrap-policy-error: typed-reason-required")
```

</details>

#### does not start a bootstrap or declare a process runner

- does not start a bootstrap or declare a process runner
   - Expected: source does not contain `process_run`
   - Expected: source does not contain `bootstrap-from-scratch`
   - Expected: source does not contain `val BOOTSTRAP_PLANNER_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not start a bootstrap or declare a process runner")
val source = rt_file_read_text(
    "src/app/cli/bootstrap_reason_planner.spl") ?? ""
expect(source.contains("process_run")).to_equal(false)
expect(source.contains("bootstrap-from-scratch")).to_equal(false)
expect(source.contains("val BOOTSTRAP_PLANNER_")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/bootstrap_reason_planner_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering minimal bootstrap reason planner source contract.
- minimal bootstrap reason planner source contract

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a48e68e520f339704a018cab11bcce6c85ab4dca49125ff43aa357c42a38fdf1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a48e68e520f339704a018cab11bcce6c85ab4dca49125ff43aa357c42a38fdf1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a48e68e520f339704a018cab11bcce6c85ab4dca49125ff43aa357c42a38fdf1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/cli/bootstrap_reason_planner_source_spec.spl
mirror: doc/06_spec/01_unit/app/cli/bootstrap_reason_planner_source_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/app/cli/bootstrap_reason_planner_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/bootstrap_reason_planner_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/bootstrap_reason_planner_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/cli/bootstrap_reason_planner_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/cli/bootstrap_reason_planner_source_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the typed policy and canonical file facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/bootstrap_reason_planner_source_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not start a bootstrap or declare a process runner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
