# bootstrap_reason_planner_admission_source_contract_spec

> Static source contract for fail-closed bootstrap planner authorization v2.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bootstrap_reason_planner_admission_source_contract_spec

Static source contract for fail-closed bootstrap planner authorization v2.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Static source contract for fail-closed bootstrap planner authorization v2.

## Scenarios

### bootstrap reason planner v2

#### admits only the Stage 3 and Stage 4 targets

- admits only the Stage 3 and Stage 4 targets
   - Expected: source contains `target == "//bootstrap:stage3"`
   - Expected: source contains `target == "//bootstrap:stage4"`
   - Expected: source does not contain `starts_with("//bootstrap:")`
   - Expected: source does not contain `starts_with("//release:")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("admits only the Stage 3 and Stage 4 targets")
expect(source.contains("target == \"//bootstrap:stage3\"")).to_equal(true)
expect(source.contains("target == \"//bootstrap:stage4\"")).to_equal(true)
expect(source.contains("starts_with(\"//bootstrap:\")")).to_equal(false)
expect(source.contains("starts_with(\"//release:\")")).to_equal(false)
```

</details>

#### requires all four binding hashes

- requires all four binding hashes
   - Expected: source contains `--parent-compiler-sha256=`
   - Expected: source contains `--runtime-snapshot-sha256=`
   - Expected: source contains `--planner-source-closure-sha256=`
   - Expected: source contains `--planner-sha256=`
   - Expected: source contains `simple-bootstrap-authorization-v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("requires all four binding hashes")
expect(source.contains("--parent-compiler-sha256=")).to_equal(true)
expect(source.contains("--runtime-snapshot-sha256=")).to_equal(true)
expect(source.contains("--planner-source-closure-sha256=")).to_equal(true)
expect(source.contains("--planner-sha256=")).to_equal(true)
expect(source.contains("simple-bootstrap-authorization-v2")).to_equal(true)
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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35c54a0a6af88be6d439155721be2b89c62e5c6ef11739c55de1a37da946d44b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35c54a0a6af88be6d439155721be2b89c62e5c6ef11739c55de1a37da946d44b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35c54a0a6af88be6d439155721be2b89c62e5c6ef11739c55de1a37da946d44b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only the Stage 3 and Stage 4 targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires all four binding hashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
