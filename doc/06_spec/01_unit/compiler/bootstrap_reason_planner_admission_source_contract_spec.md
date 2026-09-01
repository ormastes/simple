# Contract spec: test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl` and a green Results line.

## Scenarios

### bootstrap reason planner v2

#### admits only the Stage 3 and Stage 4 targets

- admits only the Stage 3 and Stage 4 targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("admits only the Stage 3 and Stage 4 targets")
expect(source).to_contain("target == \"//bootstrap:stage3\"")        expect(source).to_contain("target == \"//bootstrap:stage4\"")        expect(source).to_not_contain("starts_with(\"//bootstrap:\")")        expect(source).to_not_contain("starts_with(\"//release:\")")
```

</details>

#### requires all four binding hashes

- requires all four binding hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("requires all four binding hashes")
expect(source).to_contain("--parent-compiler-sha256=")        expect(source).to_contain("--runtime-snapshot-sha256=")        expect(source).to_contain("--planner-source-closure-sha256=")        expect(source).to_contain("--planner-sha256=")        expect(source).to_contain("simple-bootstrap-authorization-v2")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `362f737f57f79e5e374b19bd3b7b0851d73b36f5408ff00166604c905fbc65f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `362f737f57f79e5e374b19bd3b7b0851d73b36f5408ff00166604c905fbc65f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `362f737f57f79e5e374b19bd3b7b0851d73b36f5408ff00166604c905fbc65f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only the Stage 3 and Stage 4 targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires all four binding hashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
