# must_check_tiering_spec

> Purpose: exercise the production push/bootstrap mandatory-check entrypoints and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# must_check_tiering_spec

Purpose: exercise the production push/bootstrap mandatory-check entrypoints and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/must_check_tiering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: exercise the production push/bootstrap mandatory-check entrypoints and
their bootstrap-to-push transition contract.
Audience: compiler, release, and tooling engineers.

This source-contract spec does not promote open hardware or benchmark TODOs.

## Scenarios

### Must-check tiering

#### should keep the push ledger validator fail-closed and bounded

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Run the lightweight push must-check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCT-001, REQ-MCT-003
step("Run the lightweight push must-check")
val (stdout, stderr, code) = process_run("/bin/sh", [
    "scripts/check/check-push-must-pass.shs", "--self-test"
])
val output = stdout + stderr
expect(code).to_equal(0)
expect(output).to_contain("PASS — 12 ledger fixtures checked")
```

</details>

#### should produce deterministic bootstrap-owned ledger evidence

- Run the bootstrap must-check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCT-002, REQ-MCT-003, REQ-MCT-005
step("Run the bootstrap must-check")
val (stdout, stderr, code) = process_run("/bin/sh", [
    "scripts/check/check-bootstrap-must-pass.shs", "--self-test"
])
val output = stdout + stderr
expect(code).to_equal(0)
expect(output).to_contain("phase promotion TODO preservation")
expect(output).to_contain("deterministic output checked")
```

</details>

#### should accept bootstrap-produced state through the real push ref path

- Validate the must-check ledger
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCT-004, REQ-MCT-006
step("Validate the must-check ledger")
val (stdout, stderr, code) = process_run("/bin/sh", [
    "test/01_unit/scripts/must_check_tiering_test.shs"
])
val output = stdout + stderr
expect(code).to_equal(0)
expect(output).to_contain("must-check tiering contract")
expect(output).to_contain("ref-path=")
expect(output).to_contain("installed-hook=")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-MCT-001`
- `REQ-MCT-002`
- `REQ-MCT-003`
- `REQ-MCT-004`
- `REQ-MCT-005`
- `REQ-MCT-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `66f3a6d5b32c003dfabb501f00a32f4a9f3b1aecf65ec2e4ea14cf34b03105b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66f3a6d5b32c003dfabb501f00a32f4a9f3b1aecf65ec2e4ea14cf34b03105b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66f3a6d5b32c003dfabb501f00a32f4a9f3b1aecf65ec2e4ea14cf34b03105b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/must_check_tiering_spec.spl
mirror: doc/06_spec/03_system/check/must_check_tiering_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=85 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/check/must_check_tiering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/must_check_tiering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/must_check_tiering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/must_check_tiering_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/must_check_tiering_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the push ledger validator fail-closed and bounded' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/must_check_tiering_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep the push ledger validator fail-closed and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/must_check_tiering_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should produce deterministic bootstrap-owned ledger evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/must_check_tiering_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should produce deterministic bootstrap-owned ledger evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/must_check_tiering_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept bootstrap-produced state through the real push ref path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/must_check_tiering_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept bootstrap-produced state through the real push ref path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
