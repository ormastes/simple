# SPipe transactional refactor and recovery

> Crash at lock, token consumption, before-image fsync, Prepared, each replace,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe transactional refactor and recovery

Crash at lock, token consumption, before-image fsync, Prepared, each replace,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirement map
- Identity/registry: REQ-SPKC-002, 005; NFR-SPKC-009..010, 023.
- Plan/apply/recovery: REQ-SPKC-019..020, 026, 029; NFR-SPKC-004..006, 008.
- Evidence/platform: NFR-SPKC-019..022.

## Fault matrix
Crash at lock, token consumption, before-image fsync, Prepared, each replace,
file/directory fsync, Applying, validation, manifest switch, Committed, receipt
fsync, and unlock. Also cover partial write, disk full, permission loss,
revocation, concurrent edit, kill/reboot, replay/expired token, symlink swap,
unknown journal major, and cross-device move. Expected typed outcomes are
`precondition_failed`, `unauthorized`, `transaction_conflict`,
`recovery_required`, `unsupported_version`, or exact `rolled_back`; never a
mixed state reported healthy.

## Generation
`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl --output doc/06_spec --no-index`

## Scenarios

### SPipe refactor transaction and recovery

#### apply one snapshot-bound single-use approved transaction

- Apply a transactional refactor
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-002
# @req REQ-SPKC-019..020
# @req: REQ-SPKC-002, REQ-SPKC-019, REQ-SPKC-005
step("Apply a transactional refactor")
setup_spipe_knowledge_fixture()
check_spipe_refactor_recovery()
```

</details>

<details>
<summary>Advanced: recover exact old or new state at every durability boundary</summary>

#### recover exact old or new state at every durability boundary

- Apply a transactional refactor
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-019, REQ-SPKC-020, REQ-SPKC-029
step("Apply a transactional refactor")
fail("DESIGN-SCAFFOLD: inject every crash/race/fault and compare bytes metadata graph aliases and hashes")
```

</details>


</details>

<details>
<summary>Advanced: fail closed on replay cross-worktree cross-device and symlink races</summary>

#### fail closed on replay cross-worktree cross-device and symlink races

- Apply a transactional refactor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-005, REQ-SPKC-019, REQ-SPKC-020
step("Apply a transactional refactor")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
fail("DESIGN-SCAFFOLD: assert typed rejection before attacker or other-worktree effects")
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
- `REQ-SPKC-019..020`
- `REQ-SPKC-029`
- `REQ-SPKC-019`
- `REQ-SPKC-020`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ce6374587e24ff2ebdf1b9f663a2dd3493e5537645c33577684d2707dfc1dd77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce6374587e24ff2ebdf1b9f663a2dd3493e5537645c33577684d2707dfc1dd77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce6374587e24ff2ebdf1b9f663a2dd3493e5537645c33577684d2707dfc1dd77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->
