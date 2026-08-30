# Contract spec: test/01_unit/compiler/bootstrap/vhdl_design_catalog_shared_binding_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/vhdl_design_catalog_shared_binding_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/vhdl_design_catalog_shared_binding_contract_spec.spl` |
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
`bin/simple test test/01_unit/compiler/bootstrap/vhdl_design_catalog_shared_binding_contract_spec.spl` and a green Results line.

## Scenarios

### VHDL design-catalog strict shared bindings

#### tracks the resolved symbol as a scalar id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tracks the resolved symbol as a scalar id


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks the resolved symbol as a scalar id")
val source = file_read("src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl")

expect(source).to_contain("var found_id = -1")
expect(source).to_contain("Ok(Some(SymbolId(id: found_id)))")
expect(source).to_contain("fn vhdl_catalog_mark_type(ty: MirType, mut needed: Dict<i64, bool>):")
expect(source).to_contain("fn vhdl_catalog_mark_inst_types(inst: MirInst, mut needed: Dict<i64, bool>):")
expect(source).to_contain("fn vhdl_catalog_type_def_mark_dependencies(type_def: MirTypeDef, mut needed: Dict<i64, bool>):")
expect(source).to_not_contain("var found: SymbolId? = nil")        expect(source).to_not_contain("needed: mut Dict<i64, bool>")
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

- Canonical SPipe generation for source `2b8e5774085acb2ed24890ba536d589a804b039b726c5124af53ab6141bca7b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b8e5774085acb2ed24890ba536d589a804b039b726c5124af53ab6141bca7b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b8e5774085acb2ed24890ba536d589a804b039b726c5124af53ab6141bca7b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: test/01_unit/compiler/bootstrap/vhdl_design_catalog_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/vhdl_design_catalog_shared_binding_contract_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/vhdl_design_catalog_shared_binding_contract_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks the resolved symbol as a scalar id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
