# Contract spec: test/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.spl` |
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
`bin/simple test test/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.spl` and a green Results line.

## Scenarios

### backend helper strict shared bindings

#### derives compiled output optionals without reassignment

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives compiled output optionals without reassignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("derives compiled output optionals without reassignment")
val source = file_read("src/compiler/70.backend/backend/backend_helpers.spl")

expect(source).to_contain("val oc: [u8]? = if output.has_object_code: output.object_code else: nil")
expect(source).to_contain("val asm_opt: text? = if output.has_text_output: output.text_output else: nil")
expect(source).to_not_contain("var oc: [u8]? = nil")        expect(source).to_not_contain("var asm_opt: text? = nil")
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

- Canonical SPipe generation for source `dc535ba066d39d41f542c96262aecc0dab73bec03185c389150bbf659c42e568`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc535ba066d39d41f542c96262aecc0dab73bec03185c389150bbf659c42e568`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc535ba066d39d41f542c96262aecc0dab73bec03185c389150bbf659c42e568`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: test/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives compiled output optionals without reassignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
