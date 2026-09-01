# Package Export Route Shapes Specification

> Tests covering package export route shapes resolve to their terminal declaration, qualified bare exports resolve through further re-export hops, real backend facade shape: bare and qualified export of one name, re-export root memo across modules lowered by one lowerer, package-sibling registration reaches a sibling's facade-imported type, package-sibling field types, value route through a second-level plain glob, has_ optional sugar in a sibling callable signature, bare export facade with no imports beside its declaring sibling, owner-local types in a sibling trait's method signatures, sibling impl method whose return type is a directory-sibling type, tier-aliased package: sibling impl method returning a directory-sibling type.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Package Export Route Shapes Specification

## Scenarios

### package export route shapes resolve to their terminal declaration

#### resolves through a sibling that declares the type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### resolves through a sibling that re-exports the type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_bare_export_graph(
    "export CodegenTarget",
    "export use pkg.backend.backend_types.\{CodegenTarget\}")
expect(diagnostics).to_equal("")
```

</details>

#### resolves a qualified bare export naming its sibling

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_bare_export_graph(
    "export backend_types.CodegenTarget",
    "enum CodegenTarget:\n    NativeExecutable\n    WasmModule")
expect(diagnostics).to_equal("")
```

</details>

### qualified bare exports resolve through further re-export hops

#### resolves a named re-export of a qualified bare export

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain([
    terminal, qualified_init,
    "pkg.mid|export use pkg.backend.\{CodegenTarget\}",
    "pkg.facade|export use pkg.mid.\{CodegenTarget\}",
    "pkg.consumer|use pkg.facade.\{CodegenTarget\}\nfn aot(target: CodegenTarget) -> i64:\n    1"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves a payload type reached through a glob facade of a qualified bare export

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain([
    terminal, qualified_init,
    "pkg.types_facade|export use pkg.backend.*",
    "pkg.opts|use pkg.types_facade.*\nstruct AotOptions:\n    target: CodegenTarget",
    "pkg.consumer|use pkg.opts.\{AotOptions\}\nfn aot(options: AotOptions) -> i64:\n    1"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves a payload type reached through a named import of a qualified bare export

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain([
    terminal, qualified_init,
    "pkg.opts|use pkg.backend.\{CodegenTarget\}\nstruct AotOptions:\n    target: CodegenTarget",
    "pkg.consumer|use pkg.opts.\{AotOptions\}\nfn aot(options: AotOptions) -> i64:\n    1"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves a payload type two re-export hops from the consumer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain([
    terminal, qualified_init,
    "pkg.opts|use pkg.backend.\{CodegenTarget\}\nstruct AotOptions:\n    target: CodegenTarget\nfn aot_impl(options: AotOptions) -> i64:\n    1",
    "pkg.public_compile|pub use pkg.opts.\{aot_impl\}",
    "pkg.consumer|pub use pkg.public_compile.\{aot_impl\}\nfn run() -> i64:\n    1"])
expect(diagnostics).to_equal("")
```

</details>

### real backend facade shape: bare and qualified export of one name

#### resolves when the package init carries both a bare and a qualified export

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain([
    "pkg.backend.backend_types|enum CodegenTarget:\n    NativeExecutable\n    WasmModule",
    "pkg.backend.backend_api|use pkg.backend.backend_types.\{CodegenTarget\}\nstruct Backend:\n    target: CodegenTarget",
    "pkg.backend.__init__|export BackendKind, CodegenTarget\nexport backend_api.Backend\nexport backend_api.CodegenTarget",
    "pkg.backend_types|export use pkg.backend.backend_types.*",
    "pkg.backend.interp|use pkg.backend_types.*\nclass Interp:\n    fn run(self, target: CodegenTarget) -> i64:\n        1",
    "pkg.consumer|use pkg.backend.interp.\{Interp\}\nuse lazy pkg.backend_types.\{CodegenTarget\}\nfn run(i: Interp) -> i64:\n    1"])
expect(diagnostics).to_equal("")
```

</details>

### re-export root memo across modules lowered by one lowerer

#### resolves MirType through a plain glob import of a plain glob importer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([mir_types, mir_data, interp], ["pkg.backend.interp"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves MirType for a second module after a first module used the same facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = "pkg.backend.first|use pkg.mir.mir_data.\{MirModule\}\nfn go(m: MirModule) -> i64:\n    1"
val diagnostics = lower_route_chain_sequence([mir_types, mir_data, first, interp], ["pkg.backend.first", "pkg.backend.interp"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves MirType for a second module after a first module named it through the facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = "pkg.backend.first|use pkg.mir.mir_data.*\nfn go(t: MirType) -> i64:\n    1"
val diagnostics = lower_route_chain_sequence([mir_types, mir_data, first, interp], ["pkg.backend.first", "pkg.backend.interp"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves CodegenTarget in a second-hop facade consumer after the owner module was lowered first

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([
    "pkg.backend.backend_types|enum CodegenTarget:\n    NativeExecutable\n    WasmModule",
    "pkg.backend.backend_api|use pkg.backend.backend_types.\{CodegenTarget\}\nfn api_target() -> CodegenTarget:\n    CodegenTarget.NativeExecutable",
    "pkg.backend.__init__|export backend_api.CodegenTarget\nexport backend_api.api_target",
    "pkg.opts|use pkg.backend.\{CodegenTarget\}\nstruct AotOptions:\n    target: CodegenTarget\nfn aot_impl(options: AotOptions) -> i64:\n    1",
    "pkg.public_compile|pub use pkg.opts.\{aot_impl\}",
    "pkg.driver|pub use pkg.public_compile.\{aot_impl\}\nfn run() -> i64:\n    1"],
    ["pkg.backend.backend_api", "pkg.opts", "pkg.public_compile", "pkg.driver"])
expect(diagnostics).to_equal("")
```

</details>

### package-sibling registration reaches a sibling's facade-imported type

#### resolves the sibling's facade-imported type for a consumer that names nothing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([owner, facade, sibling, port], ["pkg.backend.backend_port"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves it after another module already chased the same facade name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = "pkg.other|use pkg.frontend.\{GpuIntrinsicKind\}\nfn first(k: GpuIntrinsicKind) -> i64:\n    1"
val diagnostics = lower_route_chain_sequence([owner, facade, sibling, port, first], ["pkg.other", "pkg.backend.gpu_intrinsics", "pkg.backend.backend_port"])
expect(diagnostics).to_equal("")
```

</details>

### package-sibling field types

#### resolves a sibling-declared field type of an imported struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([
    "pkg.hir.hir_definitions|struct HirImpl:\n    id: i64",
    "pkg.hir.hir_types|struct HirModule:\n    impls: [HirImpl]",
    "pkg.backend.consumer|use pkg.hir.hir_types.\{HirModule\}\nfn run(m: HirModule) -> i64:\n    1"],
    ["pkg.backend.consumer"])
expect(diagnostics).to_equal("")
```

</details>

### value route through a second-level plain glob

#### resolves a function reached only through the glob target's own glob

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([
    "pkg.frontend.parser_types_expr|struct TypeKind:\n    id: i64\nfn parser_type_kind_named_name(kind: TypeKind) -> text:\n    \"x\"",
    "pkg.frontend.parser_types|use pkg.frontend.parser_types_expr.*\nstruct Param:\n    name: text\nexport Param",
    "pkg.hir.module_surface_declarations|use pkg.frontend.parser_types.*\nfn named(kind: TypeKind) -> text:\n    parser_type_kind_named_name(kind)"],
    ["pkg.hir.module_surface_declarations"])
expect(diagnostics).to_equal("")
```

</details>

### has_ optional sugar in a sibling callable signature

#### resolves the sugared return type for a consumer that names nothing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([
    "pkg.frontend.parser_types_expr|enum GpuIntrinsicKind:\n    ThreadId\n    BlockId",
    "pkg.backend.gpu_intrinsics|use pkg.frontend.parser_types_expr.\{GpuIntrinsicKind\}\nfn recognize(name: text) -> has_GpuIntrinsicKind:\n    nil",
    "pkg.backend.feature_caps_types|struct FeatureCaps:\n    name: text"],
    ["pkg.backend.feature_caps_types"])
expect(diagnostics).to_equal("")
```

</details>

### bare export facade with no imports beside its declaring sibling

#### resolves for a zero-import sibling lowered first

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([span, definition, facade, pkg_init, context, sibling], ["pkg.blocks.sugar_registry"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves for a zero-import sibling lowered after the facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([span, definition, facade, pkg_init, context, sibling], ["pkg.blocks.blocks", "pkg.blocks.sugar_registry", "pkg.blocks.context"])
expect(diagnostics).to_equal("")
```

</details>

#### resolves for a consumer importing through the facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val consumer = "pkg.consumer|use pkg.blocks.blocks.\{Completion\}\nfn pick(c: Completion) -> text:\n    c.label"
val diagnostics = lower_route_chain_sequence([span, definition, facade, pkg_init, context, sibling, consumer], ["pkg.consumer"])
expect(diagnostics).to_equal("")
```

</details>

### owner-local types in a sibling trait's method signatures

#### array-of-owner-local default trait method return, zero-import sibling

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([definition, sibling], ["pkg.blocks.sugar_registry"])
expect(diagnostics).to_equal("")
```

</details>

#### same, after the owner was lowered first

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([definition, sibling], ["pkg.blocks.definition", "pkg.blocks.sugar_registry"])
expect(diagnostics).to_equal("")
```

</details>

### sibling impl method whose return type is a directory-sibling type

#### zero-import sibling lowered first

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([data, definition, sibling], ["pkg.blocks.sugar_registry"])
expect(diagnostics).to_equal("")
```

</details>

#### zero-import sibling lowered after the impl owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_route_chain_sequence([definition, data, sibling], ["pkg.blocks.builtin_blocks_data", "pkg.blocks.sugar_registry"])
expect(diagnostics).to_equal("")
```

</details>

### tier-aliased package: sibling impl method returning a directory-sibling type

#### zero-import sibling lowered first

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lower_aliased_chain(entries, ["pkg.blocks.sugar_registry"])).to_equal("")
```

</details>

#### zero-import sibling lowered after the impl owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lower_aliased_chain(entries, ["pkg.blocks.builtin_blocks_data", "pkg.blocks.sugar_registry"])).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/package_export_route_shapes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering package export route shapes resolve to their terminal declaration, qualified bare exports resolve through further re-export hops, real backend facade shape: bare and qualified export of one name, re-export root memo across modules lowered by one lowerer, package-sibling registration reaches a sibling's facade-imported type, package-sibling field types, value route through a second-level plain glob, has_ optional sugar in a sibling callable signature, bare export facade with no imports beside its declaring sibling, owner-local types in a sibling trait's method signatures, sibling impl method whose return type is a directory-sibling type, tier-aliased package: sibling impl method returning a directory-sibling type.
- package export route shapes resolve to their terminal declaration
- qualified bare exports resolve through further re-export hops
- real backend facade shape: bare and qualified export of one name
- re-export root memo across modules lowered by one lowerer
- package-sibling registration reaches a sibling's facade-imported type
- package-sibling field types
- value route through a second-level plain glob
- has_ optional sugar in a sibling callable signature
- bare export facade with no imports beside its declaring sibling
- owner-local types in a sibling trait's method signatures
- sibling impl method whose return type is a directory-sibling type
- tier-aliased package: sibling impl method returning a directory-sibling type

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fb47cc099691053c9d8590d9ab2c0ed16c8b4a8585227b2cbe54361a73af3be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fb47cc099691053c9d8590d9ab2c0ed16c8b4a8585227b2cbe54361a73af3be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fb47cc099691053c9d8590d9ab2c0ed16c8b4a8585227b2cbe54361a73af3be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/hir/package_export_route_shapes_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/package_export_route_shapes_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/package_export_route_shapes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/package_export_route_shapes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/package_export_route_shapes_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/hir/package_export_route_shapes_spec.spl:54:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'resolves through a sibling that declares the type' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/package_export_route_shapes_spec.spl:63:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'resolves through a sibling that re-exports the type' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/package_export_route_shapes_spec.spl:70:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'resolves a qualified bare export naming its sibling' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/package_export_route_shapes_spec.spl:111:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'resolves a named re-export of a qualified bare export' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
