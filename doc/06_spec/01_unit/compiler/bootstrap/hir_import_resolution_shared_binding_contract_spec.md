# Contract spec: test/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.spl` |
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
`bin/simple test test/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.spl` and a green Results line.

## Scenarios

### HIR import resolution strict shared bindings

#### returns the module and canonical name as one immutable result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the module and canonical name as one immutable result


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the module and canonical name as one immutable result")
val source = file_read("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")

expect(source).to_contain("struct HirResolvedImportModule:")
expect(source).to_contain("found: bool\n    imported_module: Module")
expect(source).to_contain("me resolve_import_module(importer: Module, import_name: text) -> HirResolvedImportModule:")
expect(source).to_contain("val direct_module: Module? = self.modules_by_name.get(import_name)")
expect(source).to_contain("val relative_name = hir_relative_import_name(importer.name, import_name)")
expect(source).to_contain("val package_name = segments.slice(0, keep).join(\".\")")
expect(source).to_not_contain("package_segments.push")        expect(source).to_contain("val relative_module: Module? = self.modules_by_name.get(relative_name)")
expect(source).to_contain("val fallback_name = self.resolve_module_key(import_name)")
expect(source).to_contain("val fallback_module: Module? = self.modules_by_name.get(fallback_name)")
expect(source).to_contain("val resolved_import = self.resolve_import_module(module, imp.module)")
expect(source).to_contain("if resolved_import.found:\n                val imported_mod = resolved_import.imported_module")
expect(source).to_not_contain("var imported_mod: Module?")        expect(source).to_not_contain("var resolved_module_name = imp.module")
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

- Canonical SPipe generation for source `b5c36ebc878f9674406b89c9151f39ad07ea4e8accd205aa9bd0040b97a26c75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5c36ebc878f9674406b89c9151f39ad07ea4e8accd205aa9bd0040b97a26c75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5c36ebc878f9674406b89c9151f39ad07ea4e8accd205aa9bd0040b97a26c75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: test/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the module and canonical name as one immutable result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
