# callable_signature_owner_imports_dependency_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# callable_signature_owner_imports_dependency_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### a callable's owner imports every type its signature names

#### MirType owners import it (largest sub-group, 87 of the 291)

- Verify: MirType owners import it (largest sub-group, 87 of the 291)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: MirType owners import it (largest sub-group, 87 of the 291)")
# @req: REQ-SSPEC-LOCAL-001
# 36 owner modules across 50.mir / 55.borrow / 60.mir_opt / 70.backend /
# 90.tools. Three representatives, one per layer, plus the guard.
expect(names_in_signature(
    "src/compiler/70.backend/backend/common/type_mapper.spl",
    "MirType")).to_be_true()
expect(imports_name(
    "src/compiler/70.backend/backend/common/type_mapper.spl",
    "compiler.mir.mir_types.", "MirType")).to_be_true()
expect(imports_name(
    "src/compiler/60.mir_opt/mir_opt/gvn.spl",
    "compiler.mir.mir_types.", "MirType")).to_be_true()
expect(imports_name(
    "src/compiler/90.tools/header_gen/c_header.spl",
    "compiler.mir.mir_types.", "MirType")).to_be_true()
```

</details>

#### CodegenTarget owners import it (113 of the 291)

- Verify: CodegenTarget owners import it (113 of the 291)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: CodegenTarget owners import it (113 of the 291)")
expect(names_in_signature(
    "src/compiler/70.backend/backend/llvm_type_mapper.spl",
    "CodegenTarget")).to_be_true()
expect(imports_name(
    "src/compiler/70.backend/backend/llvm_type_mapper.spl",
    "compiler.backend.backend.backend_types.",
    "CodegenTarget")).to_be_true()
expect(imports_name(
    "src/compiler/70.backend/backend/wasm_backend.spl",
    "compiler.backend.backend.backend_types.",
    "CodegenTarget")).to_be_true()
```

</details>

#### inline-asm operand types are imported by their C/LLVM owners

- Verify: inline-asm operand types are imported by their C/LLVM owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: inline-asm operand types are imported by their C/LLVM owners")
expect(imports_name(
    "src/compiler/70.backend/backend/c_backend_translate_ops.spl",
    "compiler.frontend.parser_types_expr.", "AsmLocation")).to_be_true()
expect(imports_name(
    "src/compiler/70.backend/backend/c_backend_translate_ops.spl",
    "compiler.frontend.parser_types_expr.",
    "AsmConstraintKind")).to_be_true()
expect(imports_name(
    "src/compiler/70.backend/backend/mir_to_llvm_helpers.spl",
    "compiler.frontend.parser_types_expr.", "AsmLocation")).to_be_true()
```

</details>

#### HIR and layout types are imported by their non-declaring owners

- Verify: HIR and layout types are imported by their non-declaring owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: HIR and layout types are imported by their non-declaring owners")
expect(imports_name(
    "src/compiler/35.semantics/layer_eq_validation.spl",
    "compiler.types.type_layout.", "TypeLayout")).to_be_true()
expect(imports_name(
    "src/compiler/35.semantics/const_eval.spl",
    "compiler.hir.hir_definitions.", "HirIfArm")).to_be_true()
expect(imports_name(
    "src/compiler/35.semantics/macro_check/mod.spl",
    "compiler.hir.hir_definitions.", "HirExpr")).to_be_true()
expect(imports_name(
    "src/compiler/50.mir/_MirLowering/bootstrap_type_registration.spl",
    "compiler.hir.hir_types.", "HirModule")).to_be_true()
expect(imports_name(
    "src/compiler/40.mono/instantiation.spl",
    "compiler.common.compilation_context.",
    "CompilationContext")).to_be_true()
expect(imports_name(
    "src/compiler/20.hir/hir_lowering/module_surface_types.spl",
    "compiler.frontend.parser_types.", "Export")).to_be_true()
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `838cb747d27fcb0bec8db160188ce666a3a80e39481da34cbf97c7c563aad4ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `838cb747d27fcb0bec8db160188ce666a3a80e39481da34cbf97c7c563aad4ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `838cb747d27fcb0bec8db160188ce666a3a80e39481da34cbf97c7c563aad4ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MirType owners import it (largest sub-group, 87 of the 291)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CodegenTarget owners import it (113 of the 291)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inline-asm operand types are imported by their C/LLVM owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.spl. -->
