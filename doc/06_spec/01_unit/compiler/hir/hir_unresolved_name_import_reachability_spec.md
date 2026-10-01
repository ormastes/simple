# HIR `unresolved name` import-reachability guard (run13 lane)

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR `unresolved name` import-reachability guard (run13 lane)

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### HIR unresolved-name import reachability

#### module_surface_declarations imports the parser TypeKind accessors directly

- Verify: module_surface_declarations imports the parser TypeKind accessors directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: module_surface_declarations imports the parser TypeKind accessors directly")
val p = "src/compiler/20.hir/hir_lowering/module_surface_declarations.spl"
expect(imports_naming(p, "parser_type_kind_named_name")).to_be_true()
expect(imports_naming(p, "parser_type_kind_array_element_name")).to_be_true()
```

</details>

#### suspension_analysis imports expr_kind/stmt_kind directly

- Verify: suspension_analysis imports expr_kind/stmt_kind directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: suspension_analysis imports expr_kind/stmt_kind directly")
# @req: REQ-SSPEC-LOCAL-001
val p = "src/compiler/10.frontend/desugar/suspension_analysis.spl"
expect(imports_naming(p, "expr_kind")).to_be_true()
expect(imports_naming(p, "stmt_kind")).to_be_true()
```

</details>

#### the module_surface barrel re-exports the symbols its consumers call

- Verify: the module_surface barrel re-exports the symbols its consumers call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: the module_surface barrel re-exports the symbols its consumers call")
val p = "src/compiler/20.hir/hir_lowering/module_surface.spl"
expect(imports_naming(p, "module_surface_export_origin_index_lookup")).to_be_true()
expect(imports_naming(p, "module_surfaces_frozen_alignment")).to_be_true()
```

</details>

#### module_state names make_core_decl in its ast_types import list

- Verify: module_state names make_core_decl in its ast_types import list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: module_state names make_core_decl in its ast_types import list")
val p = "src/compiler/10.frontend/core/_Ast/module_state.spl"
expect(imports_naming(p, "make_core_decl")).to_be_true()
```

</details>

#### module_declarations_bootstrap takes STMT_* from the defining module, not the package __init__

- Verify: module_declarations_bootstrap takes STMT_* from the defining module, not the package __init__


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: module_declarations_bootstrap takes STMT_* from the defining module, not the package __init__")
val p = "src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl"
expect(read_file(p).contains("use compiler.core.ast_stmt.{STMT_EXPR")).to_be_true()
```

</details>

#### MIR callers import their helpers directly

- Verify: MIR callers import their helpers directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: MIR callers import their helpers directly")
expect(imports_naming(
    "src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl",
    "bootstrap_mir_logical_module_name")).to_be_true()
expect(imports_naming(
    "src/compiler/70.backend/backend/cranelift_codegen_adapter.spl",
    "mir_operand_const_int")).to_be_true()
```

</details>

#### link.spl imports TargetOS and is_windows at module level, not inside a function

- Verify: link.spl imports TargetOS and is_windows at module level, not inside a function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: link.spl imports TargetOS and is_windows at module level, not inside a function")
val p = "src/compiler/70.backend/linker/link.spl"
expect(module_imports_naming(p, "TargetOS")).to_be_true()
expect(module_imports_naming(p, "is_windows")).to_be_true()
expect(read_file(p).contains("    use std.platform.")).to_be_false()
```

</details>

#### codegen.spl imports JitInstantiator/JitInstantiatorConfig at module level

- Verify: codegen.spl imports JitInstantiator/JitInstantiatorConfig at module level


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: codegen.spl imports JitInstantiator/JitInstantiatorConfig at module level")
val p = "src/compiler/70.backend/codegen.spl"
expect(module_imports_naming(p, "JitInstantiator")).to_be_true()
expect(module_imports_naming(p, "JitInstantiatorConfig")).to_be_true()
expect(read_file(p).contains("        use compiler.loader.jit_instantiator")).to_be_false()
```

</details>

#### hir_codec_support imports exit explicitly rather than as an ambient builtin

- Verify: hir_codec_support imports exit explicitly rather than as an ambient builtin


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: hir_codec_support imports exit explicitly rather than as an ambient builtin")
# @req: REQ-SSPEC-LOCAL-001
expect(module_imports_naming(
    "src/compiler/20.hir/hir_codec_support.spl",
    "use std.nogc_sync_mut.io_runtime.{{exit}}")).to_be_true()
```

</details>

#### parser_decls_use imports char_code from string_core

- Verify: parser_decls_use imports char_code from string_core


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: parser_decls_use imports char_code from string_core")
# @req: REQ-SSPEC-LOCAL-001
expect(module_imports_naming(
    "src/compiler/10.frontend/core/parser_decls_use.spl",
    "use std.string_core.{{char_code}}")).to_be_true()
```

</details>

#### the driver takes file_lock/file_unlock from their owner, not the colliding std.io barrel

- Verify: the driver takes file_lock/file_unlock from their owner, not the colliding std.io barrel


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: the driver takes file_lock/file_unlock from their owner, not the colliding std.io barrel")
for p in ["src/compiler/80.driver/driver_source_pipeline_parsing.spl",
          "src/compiler/80.driver/driver_hir_cache.spl"]:
    expect(read_file(p).contains("use std.io.file_ops.{{file_lock, file_unlock}}")).to_be_true()
    expect(read_file(p).contains("use std.io.{{file_lock")).to_be_false()
```

</details>

#### generated visitors call an imported exit, never the undefined `raise`

- Verify: generated visitors call an imported exit, never the undefined `raise`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: generated visitors call an imported exit, never the undefined `raise`")
for p in ["src/compiler/20.hir/generated/hir_visitor.spl",
          "src/compiler/20.hir/generated/hir_visit.spl",
          "src/compiler/10.frontend/generated/ast_visitor.spl"]:
    expect(read_file(p).contains("use std.nogc_sync_mut.io_runtime.{{exit}}")).to_be_true()
    expect(read_file(p).contains("raise \"")).to_be_false()
```

</details>

#### the generators that emit those visitors emit the exit import too

- Verify: the generators that emit those visitors emit the exit import too


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: the generators that emit those visitors emit the exit import too")
for p in ["src/app/compiler_schema/fold_gen.spl",
          "src/app/compiler_schema/visitor_gen.spl"]:
    val src = read_file(p)
    expect(src.contains("io_runtime.{{{{exit}}}}")).to_be_true()
    expect(src.contains("raise \\\"")).to_be_false()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb31ffcac76fe4d3955f370871fc652a47d6158c8bbc7ebd201e2f21bdd1b434`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb31ffcac76fe4d3955f370871fc652a47d6158c8bbc7ebd201e2f21bdd1b434`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb31ffcac76fe4d3955f370871fc652a47d6158c8bbc7ebd201e2f21bdd1b434`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module_surface_declarations imports the parser TypeKind accessors directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'suspension_analysis imports expr_kind/stmt_kind directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the module_surface barrel re-exports the symbols its consumers call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl. -->
