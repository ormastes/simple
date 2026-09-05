# SPipe transactional refactor and recovery

> Crash at each snapshot replace, restart mid-application, and manifest switch

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe transactional refactor and recovery

Crash at each snapshot replace, restart mid-application, and manifest switch

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirement map
- Identity/registry: REQ-SPKC-002, REQ-SPKC-005.
- Plan/apply/recovery substrate: REQ-SPKC-019, REQ-SPKC-020, REQ-SPKC-029.

## Fault matrix (pinned by the snapshot boundary/restart suites)
Crash at each snapshot replace, restart mid-application, and manifest switch
recover exact old or new state; never a mixed state reported healthy.

## Generation
`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl --output doc/06_spec --no-index`

## Scenarios

### SPipe refactor transaction and recovery

#### identity, registry, and receipt substrate stays canonical and green

- Run the parser identity, workspace storage, and receipt vector suites
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-002 REQ-SPKC-005
step("Run the parser identity, workspace storage, and receipt vector suites")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/unit/parser_identity_test.js test/unit/workspace_storage_test.js test/unit/operation_receipt_vector_test.js"])
expect(code).to_equal(0)  # oracle: 19/19 subtests green
expect(stdout).to_contain("# tests 19")  # oracle: all three suites executed
expect(stdout).to_contain("# fail 0")  # oracle: canonical identity never regressed
```

</details>

<details>
<summary>Advanced: snapshot recovery recovers exact old or new state at every durability boundary</summary>

#### snapshot recovery recovers exact old or new state at every durability boundary

- Run the snapshot boundary and restart recovery suites
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-019 REQ-SPKC-020 REQ-SPKC-029
step("Run the snapshot boundary and restart recovery suites")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/unit/graph_snapshot_boundary_test.js test/unit/graph_snapshot_restart_test.js"])
expect(code).to_equal(0)  # oracle: boundary + restart recovery both green
expect(stdout).to_contain("# tests 4")  # oracle: both suites executed in full
expect(stdout).to_contain("# fail 0")  # oracle: no mixed state survives recovery
```

</details>


</details>

<details>
<summary>Advanced: fail closed: no refactor transaction command is exposed before the wave lands</summary>

#### fail closed: no refactor transaction command is exposed before the wave lands

- Probe spipe --help and the release policy suite
   - Expected: code equals `0`
   - Expected: leaked is false
   - Expected: pol_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-005 REQ-SPKC-019
step("Probe spipe --help and the release policy suite")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node cli/spipe.js --help"])
expect(code).to_equal(0)  # oracle: released surface is healthy
val leaked = stdout.contains("transaction") or stdout.contains("refactor") or stdout.contains("rollback")
expect(leaked).to_equal(false)  # oracle: unreleased transaction surface is unreachable, so no half-applied state can be produced
val (pol_out, _pol_err, pol_code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/unit/release_policy_test.js"])
expect(pol_code).to_equal(0)  # oracle: release policy still rejects unproven surfaces
expect(pol_out).to_contain("# fail 0")  # oracle: policy suite green
```

</details>


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

- `REQ-SPKC-002`
- `REQ-SPKC-005`
- `REQ-SPKC-019`
- `REQ-SPKC-020`
- `REQ-SPKC-029`
- `REQ-SPKC-005.`
- `REQ-SPKC-029.`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9916b14d7749e37f3cd53c1dc02cb208404f2a07a635bbc074c13c4a227fdb78`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9916b14d7749e37f3cd53c1dc02cb208404f2a07a635bbc074c13c4a227fdb78`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9916b14d7749e37f3cd53c1dc02cb208404f2a07a635bbc074c13c4a227fdb78`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fail closed: no refactor transaction command is exposed before the wave lands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
