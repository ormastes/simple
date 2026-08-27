# Contract spec: test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl

> Audience: engineers owning the module under test. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl

Audience: engineers owning the module under test. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the module under test. Purpose: keep the pinned observable
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
`bin/simple test test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl` and a green Results line.

## Scenarios

### Stage 2 compiler source shape

#### keeps HIR import registries explicitly typed and initialized

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps HIR import registries explicitly typed and initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps HIR import registries explicitly typed and initialized")
val source = read_file_text("src/compiler/20.hir/hir_lowering/types.spl")
expect(source).to_contain("type HirImportedTraitsByName = {text: Trait}")
expect(source).to_contain("type HirImportedEnumsByName = {text: Enum}")
expect(source).to_contain("imported_traits: HirImportedTraitsByName")
expect(source).to_contain("imported_enums: HirImportedEnumsByName")
expect(source).to_contain("imported_enum_owners: HirImportedEnumOwners")
expect(source).to_contain("imported_traits: empty_imported_traits")
expect(source).to_contain("imported_enums: empty_imported_enums")
expect(source).to_contain("imported_enum_owners: empty_imported_enum_owners")
```

</details>

#### uses only declared MIR types for set literals

- uses only declared MIR types for set literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses only declared MIR types for set literals")
val source = read_file_text("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")
expect(source).to_contain("MirType(kind: MirTypeKind.Opaque(\"Set\"))")
expect(source).to_not_contain("MirTypeKind.Named(\"Set\"")
```

</details>

#### does not call the removed compiler coverage inventory

- does not call the removed compiler coverage inventory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not call the removed compiler coverage inventory")
val source = read_file_text("src/compiler/50.mir/mir_lowering_stmts.spl")
expect(source).to_not_contain("cond.coverage_excluded")        expect(source).to_not_contain("coverage_register_decision")        expect(source).to_not_contain("coverage_register_condition")        expect(source).to_not_contain("coverage_push_decision")        expect(source).to_not_contain("coverage_pop_decision")        expect(source).to_not_contain("coverage_emit_condition_probe")        expect(source).to_not_contain("coverage_emit_decision_probe")
```

</details>

#### keeps shared helpers required by Stage 2 callers

- keeps shared helpers required by Stage 2 callers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps shared helpers required by Stage 2 callers")
val driver = read_file_text("src/compiler/80.driver/driver_source_loading.spl")
val mir = read_file_text("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")
expect(driver).to_contain("pub fn _driver_physical_source_key(path: text)")
expect(mir).to_contain("fn enum_variant_disc(names: [text], variant: text)")
```

</details>

#### uses owned trait and CUDA size paths

- uses owned trait and CUDA size paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses owned trait and CUDA size paths")
val hir_module = read_file_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val hir_trait = read_file_text("src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl")
val cuda = read_file_text("src/compiler/70.backend/backend/cuda_type_mapper.spl")
expect(hir_module).to_not_contain("lower_trait_with_symbol")        expect(hir_module).to_not_contain("for imported_trait_name in self.imported_traits.keys():")        expect(hir_trait).to_contain("if self.imported_traits.contains_key(trait_name):")
expect(hir_trait).to_contain("self.lower_trait(self.imported_traits[trait_name])")
expect(hir_trait).to_contain("self.imported_traits = self.imported_traits.remove(trait_name)")
expect(cuda).to_not_contain(".sum()")        expect(cuda).to_contain("struct_total = struct_total + self.size_of(fields[struct_index].1)")
expect(cuda).to_contain("tuple_total = tuple_total + self.size_of(elements[tuple_index])")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `2f2674e54fb73b340899608194d41c530a7ea4dd9d4c1a5cabf62a0ed04ab33c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f2674e54fb73b340899608194d41c530a7ea4dd9d4c1a5cabf62a0ed04ab33c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f2674e54fb73b340899608194d41c530a7ea4dd9d4c1a5cabf62a0ed04ab33c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps HIR import registries explicitly typed and initialized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses only declared MIR types for set literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not call the removed compiler coverage inventory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
