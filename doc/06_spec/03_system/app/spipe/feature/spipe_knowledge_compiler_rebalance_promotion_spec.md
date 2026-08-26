# SPipe rebalancing, promotion, and generated-skill safety

> Budget-exhausted/disconnected graphs leave the prior virtual tree unchanged;

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe rebalancing, promotion, and generated-skill safety

Budget-exhausted/disconnected graphs leave the prior virtual tree unchanged;

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirement map
- Rebalancing: REQ-SPKC-021..022; NFR-SPKC-001, 011, 017, 023.
- Promotion: REQ-SPKC-023..024; NFR-SPKC-004, 006..007, 018, 021..022.
- Skill/phase/migration: REQ-SPKC-025, 028..030; NFR-SPKC-002..003, 019..025.

## Hostile cases
Budget-exhausted/disconnected graphs leave the prior virtual tree unchanged;
constraint conflicts return `constraint_conflict`; over-budget graphs return
`budget_exceeded`; physical apply without distinct approval is `unauthorized`.
Prompt injection, secrets, incompatible licenses, untrusted scope, single-
project normal promotion, semantic-provider failure, conflicting policy, and
consumer validation failure must reject publication with typed findings.

## Generation
`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl --output doc/06_spec --no-index`

## Scenarios

### SPipe organization and common-knowledge review

#### should produce deterministic connected review-only proposals

- Audit tree balance and promotion candidates
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-021..022
# @req REQ-SPKC-023..024
# @req REQ-SPKC-021..022
# @req REQ-SPKC-023..024
# @req: REQ-SPKC-021, REQ-SPKC-022
step("Audit tree balance and promotion candidates")
setup_spipe_knowledge_fixture()
check_spipe_knowledge_compiler()
```

</details>

<details>
<summary>Advanced: should preserve the prior tree on conflicts exhaustion and concurrent change</summary>

#### should preserve the prior tree on conflicts exhaustion and concurrent change

- Audit tree balance and promotion candidates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-021, REQ-SPKC-022, REQ-SPKC-029
step("Audit tree balance and promotion candidates")
fail("DESIGN-SCAFFOLD: assert constraint_conflict/budget_exceeded/stale proposal with zero physical moves")
```

</details>


</details>

<details>
<summary>Advanced: should reject unsafe promotion prompt and generated-skill content</summary>

#### should reject unsafe promotion prompt and generated-skill content

- Audit tree balance and promotion candidates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-023, REQ-SPKC-024, REQ-SPKC-025, REQ-SPKC-028
step("Audit tree balance and promotion candidates")
fail("DESIGN-SCAFFOLD: assert prompt data isolation, license/secret/trust rejection, provenance, consumer validation, and stale-skill failure")
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

- `REQ-SPKC-025`
- `REQ-SPKC-021..022;`
- `REQ-SPKC-023..024;`
- `REQ-SPKC-021..022`
- `REQ-SPKC-023..024`
- `REQ-SPKC-021`
- `REQ-SPKC-022`
- `REQ-SPKC-029`
- `REQ-SPKC-023`
- `REQ-SPKC-024`
- `REQ-SPKC-028`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9870b623def8f73c08de22caed5520d782e857841111abf694dbcdfdd99163f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9870b623def8f73c08de22caed5520d782e857841111abf694dbcdfdd99163f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9870b623def8f73c08de22caed5520d782e857841111abf694dbcdfdd99163f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=85 oracle=50
  traceability=100 evidence=65 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should produce deterministic connected review-only proposals' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the prior tree on conflicts exhaustion and concurrent change' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the prior tree on conflicts exhaustion and concurrent change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsafe promotion prompt and generated-skill content' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject unsafe promotion prompt and generated-skill content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
