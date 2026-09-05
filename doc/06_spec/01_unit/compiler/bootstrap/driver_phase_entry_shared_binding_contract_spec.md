# Contract spec: test/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.spl` |
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
`bin/simple test test/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.spl` and a green Results line.

## Scenarios

### driver phase-entry strict shared bindings

#### derives the final entry HIR from a scalar source index

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives the final entry HIR from a scalar source index


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("derives the final entry HIR from a scalar source index")
val source = file_read("src/compiler/80.driver/driver.spl")

expect(source).to_contain("var phase_entry_source_index = -1")
expect(source).to_contain("phase_entry_source_index = source_idx")
expect(source).to_contain("val phase_entry_hir: HirModule? = if phase_entry_source_index >= 0:")
expect(source).to_contain("self.ctx.bootstrap_entry_hir")
expect(source).to_not_contain("var phase_entry_hir: HirModule? = self.ctx.bootstrap_entry_hir")
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

- Canonical SPipe generation for source `88260c3ea21eb6e91eb08528ce169bf106ad4e4831eca1170d5f15220c02bd4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88260c3ea21eb6e91eb08528ce169bf106ad4e4831eca1170d5f15220c02bd4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88260c3ea21eb6e91eb08528ce169bf106ad4e4831eca1170d5f15220c02bd4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: test/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives the final entry HIR from a scalar source index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
