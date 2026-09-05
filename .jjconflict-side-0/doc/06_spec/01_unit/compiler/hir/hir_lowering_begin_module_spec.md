# Hir Lowering Begin Module Specification

> Tests covering HirLowering.begin_module.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Lowering Begin Module Specification

## Scenarios

### HirLowering.begin_module

#### retains the complete diagnostic stream after transient retirement

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains the complete diagnostic stream after transient retirement
   - Expected: rt_transient_array_scope_begin() is true
   - Expected: rt_transient_array_scope_pause() is true
   - Expected: lowering.promote_diagnostics_transient_owner() is true
   - Expected: rt_transient_array_scope_end() is true
   - Expected: lowering.errors.len() equals `1`
   - Expected: lowering.diagnostic_recovered[0] is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains the complete diagnostic stream after transient retirement")
val surfaces = ModuleSurfacesByName.from_parts(
    [ModuleSurface.empty("diagnostic")], {"diagnostic": 0},
    ["diagnostic"], [0]).unwrap()
expect(rt_transient_array_scope_begin()).to_equal(true)
var lowering = hirlowering_for_module("diagnostic.spl", surfaces)
lowering.error("owned failure", Span.empty())
expect(rt_transient_array_scope_pause()).to_equal(true)
expect(lowering.promote_diagnostics_transient_owner()).to_equal(true)
expect(rt_transient_array_scope_end()).to_equal(true)
expect(lowering.errors.len()).to_equal(1)
expect(lowering.diagnostic_messages[0]).to_contain("owned failure")
expect(lowering.diagnostic_recovered[0]).to_equal(false)
```

</details>

#### resets module-local traits while preserving surfaces and configuration

- resets module-local traits while preserving surfaces and configuration
   - Expected: lowering.module_filename equals `second.spl`
   - Expected: lowering.symbols.next_symbol_id equals `0`
   - Expected: lowering.loop_depth equals `0`
   - Expected: lowering.lowered_traits.keys().len() equals `0`
   - Expected: lowering.module_surfaces.index_by_name.contains_key("first") is true
   - Expected: lowering.type_inference_config.unwrap().strict_empty_collections is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resets module-local traits while preserving surfaces and configuration")
val surfaces_result = ModuleSurfacesByName.from_parts(
    [ModuleSurface.empty("first")], {"first": 0}, ["first"], [0])
val surfaces = surfaces_result.unwrap()
var lowering = hirlowering_for_module("first.spl", surfaces)
val retained_trait = HirTrait(
    symbol: SymbolId(id: 41), name: "Retained", type_params: [],
    methods: [], supertraits: [], defaults: [], where_clause: [],
    assoc_types: [], visibility: Visibility.Public, is_public: true,
    has_doc_comment: false, doc_comment: "", span: Span.empty(),
    is_generic_template: false, has_specialization_of: false,
    specialization_of: "", type_bindings: {})
val imported_trait = ParserTrait(
    name: "ImportedTrait", type_params: [], super_traits: [],
    where_clause: [], methods: [], assoc_types: [],
    visibility: Visibility.Public, is_public: true,
    has_doc_comment: false, doc_comment: "", span: Span.empty())
val imported_enum = ParserEnum(
    name: "ImportedEnum", type_params: [], variants: [],
    visibility: Visibility.Public, is_public: true,
    has_doc_comment: false, doc_comment: "", span: Span.empty())
lowering.lowered_traits["Retained"] = retained_trait
lowering.imported_traits["ImportedTrait"] = imported_trait
lowering.imported_enums["ImportedEnum"] = imported_enum
lowering.current_function = Some(SymbolId(id: 19))
lowering.current_method_self_type = Some(HirType.named("OldSelf"))
lowering.current_method_self_symbol_id = 20
lowering.reexport_walk_complete = false
lowering.reexport_walk_valid = false
lowering.set_type_inference_config(TypeInferenceConfig.strict())
lowering.symbols.next_symbol_id = 7
lowering.loop_depth = 3
lowering.begin_module("second.spl")
expect(lowering.module_filename).to_equal("second.spl")
expect(lowering.symbols.next_symbol_id).to_equal(0)
expect(lowering.loop_depth).to_equal(0)
expect(lowering.lowered_traits.keys().len()).to_equal(0)
expect(lowering.module_surfaces.index_by_name.contains_key("first")).to_equal(true)
expect(lowering.type_inference_config.unwrap().strict_empty_collections).to_equal(true)
```

</details>

#### clears two-module transient state without leaking imports locals or glob visits

- clears two-module transient state without leaking imports locals or glob visits
   - Expected: lowering.symbols.next_symbol_id equals `0`
   - Expected: lowering.symbols.exact_symbols.keys().len() equals `0`
   - Expected: lowering.symbols.qualified_functions.keys().len() equals `0`
   - Expected: lowering.symbols.scopes.keys().len() equals `1`
   - Expected: lowering.symbols.current_scope.id equals `0`
   - Expected: lowering.loaded_modules.len() equals `0`
   - Expected: lowering.imported_traits.keys().len() equals `0`
   - Expected: lowering.imported_enums.keys().len() equals `0`
   - Expected: lowering.imported_enum_owners.keys().len() equals `0`
   - Expected: lowering.materialized_payload_origins.keys().len() equals `0`
   - Expected: lowering.materialized_payload_bindings.keys().len() equals `0`
   - Expected: lowering.local_struct_types.keys().len() equals `0`
   - Expected: lowering.struct_field_types_by_name.keys().len() equals `0`
   - Expected: lowering.struct_field_order_by_name.keys().len() equals `0`
   - Expected: lowering.local_tuple_types.keys().len() equals `0`
   - Expected: lowering.fn_tuple_returns.keys().len() equals `0`
   - Expected: lowering.enum_variant_names.keys().len() equals `0`
   - Expected: lowering.glob_expand_memo.keys().len() equals `0`
   - Expected: lowering.reexport_visit_surface_indices.len() equals `0`
   - Expected: lowering.reexport_visit_wanted.len() equals `0`
   - Expected: lowering.reexport_visit_depths.len() equals `0`
   - Expected: lowering.registering_import_symbols is false
   - Expected: lowering.current_method_self_symbol_id equals `-1`
   - Expected: lowering.reexport_walk_complete is true
   - Expected: lowering.reexport_walk_valid is true
   - Expected: lowering.diagnostic_messages.len() equals `0`
   - Expected: lowering.diagnostic_recovered.len() equals `0`
   - Expected: lowering.module_surfaces.index_by_name.contains_key("first") is true
   - Expected: lowering.lowered_traits.contains_key("Retained") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clears two-module transient state without leaking imports locals or glob visits")
val surfaces = ModuleSurfacesByName.from_parts(
    [ModuleSurface.empty("first")], {"first": 0}, ["first"], [0]).unwrap()
var lowering = hirlowering_for_module("first.spl", surfaces)
lowering.symbols.next_symbol_id = 9
lowering.symbols.exact_symbols["old"] = 8
lowering.symbols.qualified_functions["old.fn"] = 8
lowering.symbols.push_scope(ScopeKind.Function)
lowering.loaded_modules.push("old.module")
lowering.imported_enum_owners["Old"] = "owner"
lowering.materialized_payload_origins["old"] = true
lowering.materialized_payload_bindings["Old"] = "old"
lowering.local_struct_types[7] = "OldStruct"
lowering.struct_field_types_by_name["OldStruct"] = {
    "field": HirType.named("i64")}
lowering.struct_field_order_by_name["OldStruct"] = ["field"]
lowering.local_tuple_types[8] = [HirType.named("text")]
lowering.fn_tuple_returns["old_fn"] = [HirType.named("i64")]
lowering.enum_variant_names["OldVariant"] = true
lowering.glob_expand_memo["old.module"] = 3
lowering.reexport_visit_surface_indices.push(4)
lowering.reexport_visit_wanted.push("Old")
lowering.reexport_visit_depths.push(2)
lowering.registering_import_symbols = true
lowering.diagnostic_messages.push("old diagnostic")
lowering.diagnostic_recovered.push(true)

lowering.begin_module("second.spl")
expect(lowering.symbols.next_symbol_id).to_equal(0)
expect(lowering.symbols.exact_symbols.keys().len()).to_equal(0)
expect(lowering.symbols.qualified_functions.keys().len()).to_equal(0)
expect(lowering.symbols.scopes.keys().len()).to_equal(1)
expect(lowering.symbols.current_scope.id).to_equal(0)
expect(lowering.loaded_modules.len()).to_equal(0)
expect(lowering.imported_traits.keys().len()).to_equal(0)
expect(lowering.imported_enums.keys().len()).to_equal(0)
expect(lowering.imported_enum_owners.keys().len()).to_equal(0)
expect(lowering.materialized_payload_origins.keys().len()).to_equal(0)
expect(lowering.materialized_payload_bindings.keys().len()).to_equal(0)
expect(lowering.local_struct_types.keys().len()).to_equal(0)
expect(lowering.struct_field_types_by_name.keys().len()).to_equal(0)
expect(lowering.struct_field_order_by_name.keys().len()).to_equal(0)
expect(lowering.local_tuple_types.keys().len()).to_equal(0)
expect(lowering.fn_tuple_returns.keys().len()).to_equal(0)
expect(lowering.enum_variant_names.keys().len()).to_equal(0)
expect(lowering.glob_expand_memo.keys().len()).to_equal(0)
expect(lowering.reexport_visit_surface_indices.len()).to_equal(0)
expect(lowering.reexport_visit_wanted.len()).to_equal(0)
expect(lowering.reexport_visit_depths.len()).to_equal(0)
expect(lowering.registering_import_symbols).to_equal(false)
expect(lowering.current_function).to_be_nil()
expect(lowering.current_method_self_type).to_be_nil()
expect(lowering.current_method_self_symbol_id).to_equal(-1)
expect(lowering.reexport_walk_complete).to_equal(true)
expect(lowering.reexport_walk_valid).to_equal(true)
expect(lowering.diagnostic_messages.len()).to_equal(0)
expect(lowering.diagnostic_recovered.len()).to_equal(0)
expect(lowering.module_surfaces.index_by_name.contains_key("first")).to_equal(true)
expect(lowering.lowered_traits.contains_key("Retained")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HirLowering.begin_module.
- HirLowering.begin_module

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `bd87caf8db5b164e4ceb38e4ad4ac32789e1c3e8fdaf8be2fb8ea7f2fd20275f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd87caf8db5b164e4ceb38e4ad4ac32789e1c3e8fdaf8be2fb8ea7f2fd20275f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd87caf8db5b164e4ceb38e4ad4ac32789e1c3e8fdaf8be2fb8ea7f2fd20275f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_lowering_begin_module_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_lowering_begin_module_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_lowering_begin_module_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains the complete diagnostic stream after transient retirement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resets module-local traits while preserving surfaces and configuration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears two-module transient state without leaking imports locals or glob visits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
