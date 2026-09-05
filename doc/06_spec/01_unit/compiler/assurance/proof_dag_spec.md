# proof_dag_spec

> Purpose: Prove that FV2 proof dependency DAG.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# proof_dag_spec

Purpose: Prove that FV2 proof dependency DAG.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/proof_dag_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that FV2 proof dependency DAG.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### FV2 proof dependency DAG

#### schedules dependencies before consumers and reports the critical path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- schedules dependencies before consumers and reports the critical path
- Verify: schedules dependencies before consumers and reports the critical path
   - Expected: schedule.diagnostic equals ``
   - Expected: schedule.ordered_components.len() equals `3`
   - Expected: schedule.ordered_components[0].symbol_ids[0] equals `type`
   - Expected: schedule.ordered_components[2].symbol_ids[0] equals `api`
   - Expected: schedule.critical_path_ms equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("schedules dependencies before consumers and reports the critical path")
step("Verify: schedules dependencies before consumers and reports the critical path")
# @req: REQ-COMP-FV2-PROOF-DEPENDENCY-DAG-001
val schedule = build_proof_dag_schedule_v1([
    ProofDagNodeV1("api", ["logic"], "api-hash", 3),
    ProofDagNodeV1("logic", ["type"], "logic-hash", 5),
    ProofDagNodeV1("type", [], "type-hash", 2)
])
expect(schedule.diagnostic).to_equal("")
expect(schedule.ordered_components.len()).to_equal(3)
expect(schedule.ordered_components[0].symbol_ids[0]).to_equal("type")
expect(schedule.ordered_components[2].symbol_ids[0]).to_equal("api")
expect(schedule.critical_path_ms).to_equal(10)
```

</details>

#### collapses recursive proof roots into one SCC

- collapses recursive proof roots into one SCC
- Verify: collapses recursive proof roots into one SCC
   - Expected: schedule.diagnostic equals ``
   - Expected: schedule.ordered_components.len() equals `1`
   - Expected: schedule.ordered_components[0].symbol_ids.join(",") equals `even,odd`
   - Expected: schedule.critical_path_ms equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collapses recursive proof roots into one SCC")
step("Verify: collapses recursive proof roots into one SCC")
val schedule = build_proof_dag_schedule_v1([
    ProofDagNodeV1("even", ["odd"], "even-hash", 4),
    ProofDagNodeV1("odd", ["even"], "odd-hash", 6)
])
expect(schedule.diagnostic).to_equal("")
expect(schedule.ordered_components.len()).to_equal(1)
expect(schedule.ordered_components[0].symbol_ids.join(",")).to_equal("even,odd")
expect(schedule.critical_path_ms).to_equal(10)
```

</details>

#### invalidates only the changed symbol and its reverse dependency closure

- invalidates only the changed symbol and its reverse dependency closure
- Verify: invalidates only the changed symbol and its reverse dependency closure
   - Expected: proof_dag_affected_symbols(nodes, ["type"]).join(",") equals `api,logic,type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("invalidates only the changed symbol and its reverse dependency closure")
step("Verify: invalidates only the changed symbol and its reverse dependency closure")
val nodes = [
    ProofDagNodeV1("unrelated", [], "u", 1),
    ProofDagNodeV1("api", ["logic"], "a", 1),
    ProofDagNodeV1("logic", ["type"], "l", 1),
    ProofDagNodeV1("type", [], "t", 1)
]
expect(proof_dag_affected_symbols(nodes, ["type"]).join(",")).to_equal("api,logic,type")
```

</details>

#### fails closed on a missing transitive dependency

- fails closed on a missing transitive dependency
- Verify: fails closed on a missing transitive dependency


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed on a missing transitive dependency")
step("Verify: fails closed on a missing transitive dependency")
val schedule = build_proof_dag_schedule_v1([
    ProofDagNodeV1("api", ["unchecked-helper"], "api-hash", 1)
])
expect(schedule.diagnostic).to_contain("DEPENDENCY")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-FV2-PROOF-DEPENDENCY-DAG-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd81adc8b3e75b3c451bafae2f5a24bec66e74073aa23aff3b5134a889dc20fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd81adc8b3e75b3c451bafae2f5a24bec66e74073aa23aff3b5134a889dc20fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd81adc8b3e75b3c451bafae2f5a24bec66e74073aa23aff3b5134a889dc20fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/assurance/proof_dag_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/proof_dag_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/proof_dag_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/proof_dag_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/proof_dag_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/assurance/proof_dag_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'schedules dependencies before consumers and reports the critical path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/proof_dag_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses recursive proof roots into one SCC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/proof_dag_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates only the changed symbol and its reverse dependency closure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
