# Stage2 Source Shape Regression Specification

> Tests covering Stage 2 compiler source shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage2 Source Shape Regression Specification

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
expect(source.contains("MirTypeKind.Named(\"Set\"")).to_be(false)
```

</details>

#### does not call the removed compiler coverage inventory

- does not call the removed compiler coverage inventory


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not call the removed compiler coverage inventory")
val source = read_file_text("src/compiler/50.mir/mir_lowering_stmts.spl")
expect(source.contains("cond.coverage_excluded")).to_be(false)
expect(source.contains("coverage_register_decision")).to_be(false)
expect(source.contains("coverage_register_condition")).to_be(false)
expect(source.contains("coverage_push_decision")).to_be(false)
expect(source.contains("coverage_pop_decision")).to_be(false)
expect(source.contains("coverage_emit_condition_probe")).to_be(false)
expect(source.contains("coverage_emit_decision_probe")).to_be(false)
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

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses owned trait and CUDA size paths")
val hir_module = read_file_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val hir_trait = read_file_text("src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl")
val cuda = read_file_text("src/compiler/70.backend/backend/cuda_type_mapper.spl")
expect(hir_module.contains("lower_trait_with_symbol")).to_be(false)
expect(hir_module.contains("for imported_trait_name in self.imported_traits.keys():")).to_be(false)
expect(hir_trait).to_contain("if self.imported_traits.contains_key(trait_name):")
expect(hir_trait).to_contain("self.lower_trait(self.imported_traits[trait_name])")
expect(hir_trait).to_contain("self.imported_traits = self.imported_traits.remove(trait_name)")
expect(cuda.contains(".sum()")).to_be(false)
expect(cuda).to_contain("struct_total = struct_total + self.size_of(fields[struct_index].1)")
expect(cuda).to_contain("tuple_total = tuple_total + self.size_of(elements[tuple_index])")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage 2 compiler source shape.
- Stage 2 compiler source shape

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3899f40d4fc9a0842f8cc854e31ae798868123fd67b1bd18a6cb845a42f82297`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3899f40d4fc9a0842f8cc854e31ae798868123fd67b1bd18a6cb845a42f82297`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3899f40d4fc9a0842f8cc854e31ae798868123fd67b1bd18a6cb845a42f82297`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps HIR import registries explicitly typed and initialized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses only declared MIR types for set literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not call the removed compiler coverage inventory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
