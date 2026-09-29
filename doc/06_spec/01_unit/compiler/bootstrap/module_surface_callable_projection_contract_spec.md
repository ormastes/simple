# module_surface_callable_projection_contract_spec

> Bootstrap contract for reference-semantic callable surface payloads.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# module_surface_callable_projection_contract_spec

Bootstrap contract for reference-semantic callable surface payloads.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Bootstrap contract for reference-semantic callable surface payloads.

## Scenarios

### module surface callable projection

#### retains callable payloads as reference-semantic classes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains callable payloads as reference-semantic classes
   - Expected: types does not contain `struct ModuleSurfaceCallable:`
   - Expected: types does not contain `callable_values: [ModuleSurfaceCallable]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains callable payloads as reference-semantic classes")
val types = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/module_surface_types.spl") ?? ""
expect(types).to_contain("class ModuleSurfaceCallable:")
expect(types.contains("struct ModuleSurfaceCallable:")).to_equal(false)
expect(types.contains("callable_values: [ModuleSurfaceCallable]")).to_equal(false)
```

</details>

#### does not recover imported callable payloads through Dict indexing

- does not recover imported callable payloads through Dict indexing
   - Expected: registration does not contain `imported_mod.callables[imported_name]`
   - Expected: materialization does not contain `impl_.methods[method_name]`
   - Expected: materialization does not contain `for trait_method in trait_.methods`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not recover imported callable payloads through Dict indexing")
val registration = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl") ?? ""
expect(registration.contains("imported_mod.callables[imported_name]")).to_equal(false)
expect(registration).to_contain("module_surface_signature_index")
val materialization = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl") ?? ""
expect(materialization.contains("impl_.methods[method_name]")).to_equal(false)
expect(materialization.contains("for trait_method in trait_.methods")).to_equal(false)
```

</details>

#### uses frozen scalar routes for cross-stage import traversal

- uses frozen scalar routes for cross-stage import traversal
   - Expected: materialization does not contain `facade_mod.imports`
   - Expected: materialization does not contain `surfaces[owner_index].imports`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses frozen scalar routes for cross-stage import traversal")
val materialization = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl") ?? ""
expect(materialization).to_contain("import_route_item_offsets")
expect(materialization).to_contain("import_route_item_local_names")
expect(materialization.contains("facade_mod.imports")).to_equal(false)
expect(materialization.contains("surfaces[owner_index].imports")).to_equal(false)
```

</details>

#### uses frozen scalar routes for primary import registration

- uses frozen scalar routes for primary import registration
   - Expected: resolution does not contain `.imports[`
   - Expected: resolution does not contain `.items[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses frozen scalar routes for primary import registration")
val resolution = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl") ?? ""
expect(resolution).to_contain("import_route_module_names")
expect(resolution).to_contain("import_route_item_offsets")
expect(resolution.contains(".imports[")).to_equal(false)
expect(resolution.contains(".items[")).to_equal(false)
```

</details>

#### discovers declaration kinds through frozen scalar names

- discovers declaration kinds through frozen scalar names


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("discovers declaration kinds through frozen scalar names")
val registration = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl") ?? ""
expect(registration).to_contain("module_surface_composite_index")
expect(registration).to_contain("imported_mod.enum_names.contains")
expect(registration).to_contain("imported_mod.trait_names.contains")
expect(registration).to_contain("imported_mod.type_alias_names.contains")
expect(registration).to_contain("imported_mod.constant_names.contains")
```

</details>

#### projects composite fields without reopening retained payload dictionaries

- projects composite fields without reopening retained payload dictionaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects composite fields without reopening retained payload dictionaries")
val registration = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl") ?? ""
expect(registration).to_contain("composite_projection.field_offsets")
expect(registration).to_contain("composite_projection.dependency_names")
expect(registration.contains("imported_mod.composites[imported_name]")).to_be(false)
expect(registration.contains("for field in composite.fields")).to_be(false)
val declarations = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/module_surface_declarations.spl") ?? ""
expect(declarations).to_contain("module_surface_composite_projection_append")
expect(declarations.contains("composites[composite_name]")).to_be(false)
```

</details>

#### uses scalar qualified symbol indexes for staged lookup

- uses scalar qualified symbol indexes for staged lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses scalar qualified symbol indexes for staged lookup")
val symbols = rt_file_read_text("src/compiler/20.hir/hir_types.spl") ?? ""
expect(symbols).to_contain("qualified_type_names: [text]")
expect(symbols).to_contain("qualified_type_ids: [i64]")
expect(symbols).to_contain("qualified_function_names: [text]")
expect(symbols).to_contain("qualified_function_ids: [i64]")
expect(symbols.contains("if self.qualified_types.has(key):")).to_be(false)
expect(symbols.contains("if self.qualified_functions.has(key):")).to_be(false)
```

</details>

#### projects imported aggregate types through staged-safe branch assignment

- projects imported aggregate types through staged-safe branch assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects imported aggregate types through staged-safe branch assignment")
val lowering = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl") ?? ""
expect(lowering).to_contain(
    "var element: HirType = HirType(kind: HirTypeKind.Error")
expect(lowering).to_contain("element = HirType(")
expect(lowering).to_contain("var projected: HirType = element")
expect(lowering.contains("val element = if raw_symbol_id >= 0:")).to_be(false)
expect(lowering.contains("val element = if raw_element_id >= 0:")).to_be(false)
```

</details>

#### binds daemon closure primitives from their canonical owner

- binds daemon closure primitives from their canonical owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds daemon closure primitives from their canonical owner")
val protocol = rt_file_read_text(
    "src/std/nogc_sync_mut/daemon_sdk/protocol.spl") ?? ""
expect(protocol).to_contain(
    "use std.nogc_sync_mut.io_runtime.{dir_list}")
expect(protocol).to_contain(
    "use std.nogc_sync_mut.io_runtime.{time_now_unix_micros}")
```

</details>

#### shares one glob memo across a package sibling expansion

- shares one glob memo across a package sibling expansion


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shares one glob memo across a package sibling expansion")
val resolution = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl") ?? ""
expect(resolution).to_contain(
    "val fresh_package_memo: {text: i64} = {}")
expect(resolution).to_contain(
    "self.glob_expand_memo = fresh_package_memo")
val sibling_helper = resolution.substring(
    resolution.index_of("me register_package_sibling_symbols", 0),
    resolution.index_of("me register_glob_imported_symbols_depth", 0))
expect(sibling_helper.contains("self.glob_expand_memo =")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `dfdb0d29fc650e479d9a725dc7b96078168742131ec3d0f2cbf49606b2345d9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dfdb0d29fc650e479d9a725dc7b96078168742131ec3d0f2cbf49606b2345d9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dfdb0d29fc650e479d9a725dc7b96078168742131ec3d0f2cbf49606b2345d9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains callable payloads as reference-semantic classes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not recover imported callable payloads through Dict indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/module_surface_callable_projection_contract_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses frozen scalar routes for cross-stage import traversal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
