# PostgreSQL mimic server

> This executable scenario proves bounded PostgreSQL-like session/query semantics

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PostgreSQL mimic server

This executable scenario proves bounded PostgreSQL-like session/query semantics

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/database/postgres_mimic_server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This executable scenario proves bounded PostgreSQL-like session/query semantics
over the pure-Simple database engine and the compiled-artifact deployment rule.
It does not claim PostgreSQL wire, TLS, SCRAM, COPY, or replication parity.

## Scenarios

### REQ-PGM PostgreSQL mimic server

#### should execute a PostgreSQL-like session on PureDatabase

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PGM
```

</details>

#### should select a compiled database artifact for interpreter callers

- should select a compiled database artifact for interpreter callers
- Resolve the production database execution plan
   - Expected: plan.kind == DatabaseArtifactKind.SmfExecutable is true
   - Expected: database_plan_uses_compiled_artifact(plan) is true
   - Expected: plan.production_ready is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should select a compiled database artifact for interpreter callers")
step("Resolve the production database execution plan")
val plan = database_select_plan("interpreter", false)
expect(plan.kind == DatabaseArtifactKind.SmfExecutable).to_equal(true)
expect(plan.artifact_path).to_end_with(".smf")
expect(database_plan_uses_compiled_artifact(plan)).to_equal(true)
expect(plan.production_ready).to_equal(true)
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
- `REQ-PGM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3af4f4aa133694d7d06f54c9f40688862f5b2dc0c4c79bcb2e513927705d6bc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3af4f4aa133694d7d06f54c9f40688862f5b2dc0c4c79bcb2e513927705d6bc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3af4f4aa133694d7d06f54c9f40688862f5b2dc0c4c79bcb2e513927705d6bc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/lib/database/postgres_mimic_server_spec.spl
mirror: doc/06_spec/03_system/lib/database/postgres_mimic_server_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/lib/database/postgres_mimic_server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/lib/database/postgres_mimic_server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/lib/database/postgres_mimic_server_spec.spl:20:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should execute a PostgreSQL-like session on PureDatabase' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/lib/database/postgres_mimic_server_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute a PostgreSQL-like session on PureDatabase' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/lib/database/postgres_mimic_server_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should select a compiled database artifact for interpreter callers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/lib/database/postgres_mimic_server_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should select a compiled database artifact for interpreter callers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
