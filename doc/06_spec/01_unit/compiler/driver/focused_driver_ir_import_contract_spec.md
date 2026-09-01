# Contract spec: test/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.spl` |
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
`bin/simple test test/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.spl` and a green Results line.

## Scenarios

### focused driver IR import contract

#### does not retain unused HIR or MIR owners

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val driver = file_read("src/compiler/80.driver/driver.spl")
expect(driver).to_not_contain("use compiler.hir.hir.*")        expect(driver).to_not_contain("use compiler.mir.mir.*")        expect(driver).to_not_contain("use compiler.hir.hir_types.")        expect(driver).to_not_contain("use compiler.mir.mir_instructions.")        expect(driver).to_not_contain("use compiler.backend.sffi.*")        expect(driver).to_not_contain("use compiler.common.config.*")        expect(driver).to_not_contain("use driver_types.*")        expect(driver).to_contain("use compiler.driver.driver_types.")
expect(driver).to_contain("use compiler.common.driver_core_types.")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `879c88a502c6bad186949c4c1a975ee19a4538b28107c72c192c8a03d940c253`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `879c88a502c6bad186949c4c1a975ee19a4538b28107c72c192c8a03d940c253`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `879c88a502c6bad186949c4c1a975ee19a4538b28107c72c192c8a03d940c253`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/compiler/driver/focused_driver_ir_import_contract_spec.spl:37:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not retain unused HIR or MIR owners' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
