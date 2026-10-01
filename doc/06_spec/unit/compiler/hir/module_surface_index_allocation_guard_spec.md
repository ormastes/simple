# Module Surface Index Allocation Guard Specification

> Tests covering module surface scalar index allocation guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Surface Index Allocation Guard Specification

## Scenarios

### module surface scalar index allocation guard

#### does not rebuild Dict key/value arrays in module surface lookup

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not rebuild Dict key/value arrays in module surface lookup
   - Expected: source.index_of("val names = index_by_name.keys()") equals `-1`
   - Expected: source.index_of("val indices = index_by_name.values()") equals `-1`
   - Expected: source.index_of("export_origin_index.put(") equals `-1`
   - Expected: source.index_of("origins.put(") equals `-1`
   - Expected: source.index_of("origin_index.put(") equals `-1`
   - Expected: source.index_of("surface.export_origin_index.put(") equals `-1`
   - Expected: source.index_of("revisit_surface.export_origin_index.put(") equals `-1`
   - Expected: source.index_of("revisit_origin_index_explicit.put(") equals `-1`
   - Expected: source.index_of("revisit_origin_index_sibling.put(") equals `-1`
   - Expected: source.index_of("while position < origin_index.names.len()") equals `-1`
   - Expected: source.index_of("origin_index.names[position] == name") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rebuild Dict key/value arrays in module surface lookup")
val source = read_file_text(MODULE_SURFACE)
expect(source.index_of("val names = index_by_name.keys()")).to_equal(-1)
expect(source.index_of("val indices = index_by_name.values()")).to_equal(-1)
expect(source.index_of("export_origin_index.put(")).to_equal(-1)
expect(source.index_of("origins.put(")).to_equal(-1)
expect(source.index_of("origin_index.put(")).to_equal(-1)
expect(source.index_of("surface.export_origin_index.put(")).to_equal(-1)
expect(source.index_of("revisit_surface.export_origin_index.put(")).to_equal(-1)
expect(source.index_of("revisit_origin_index_explicit.put(")).to_equal(-1)
expect(source.index_of("revisit_origin_index_sibling.put(")).to_equal(-1)
expect(source).to_contain("ordered_names: [text]")
expect(source).to_contain("ordered_indices: [i64]")
expect(source).to_contain("composite_names: [text]")
expect(source).to_contain("enum_names: [text]")
expect(source).to_contain("trait_names: [text]")
expect(source).to_contain("callable_names: [text]")
expect(source).to_contain("type_alias_names: [text]")
expect(source).to_contain("constant_names: [text]")
expect(source).to_contain("index_by_name: Dict<text, i64>")
expect(source).to_contain("origin_index.index_by_name.contains_key(name)")
expect(source).to_contain("origin_index.index_by_name[name]")
expect(source.index_of("while position < origin_index.names.len()")).to_equal(-1)
expect(source.index_of("origin_index.names[position] == name")).to_equal(-1)
expect(source).to_contain("fn module_surface_export_origin_index_put(")
expect(source).to_contain("fn module_surfaces_validate_index_alignment(")
expect(source).to_contain(
    "source: SourceFile, origins: ModuleSurfaceExportOriginIndex")
expect(source).to_contain(") -> Result<bool, text>:")
expect(source).to_contain(
    "val origin_hints = module_surface_export_origin_index_empty()")
expect(source.index_of("ModuleSurfaceExportOriginIndex.empty()"))\
    .to_equal(-1)
expect(source).to_contain("if origin_hints_result.is_err():")
expect(source.index_of("val origin_hints = origin_hints_result.unwrap()"))\
    .to_equal(-1)
```

</details>

#### uses the aligned arrays in the module lowering lookup

- uses the aligned arrays in the module lowering lookup
   - Expected: source.index_of("val names = surfaces.index_by_name.keys()") equals `-1`
   - Expected: source.index_of("val indices = surfaces.index_by_name.values()") equals `-1`
   - Expected: source.index_of("self.module_surfaces.index_by_name.keys()") equals `-1`
   - Expected: source.index_of("surfaces.composites.keys()") equals `-1`
   - Expected: source.index_of("surfaces.enums.keys()") equals `-1`
   - Expected: source.index_of("surfaces.traits.keys()") equals `-1`
   - Expected: source.index_of("surfaces.callables.keys()") equals `-1`
   - Expected: source.index_of("surfaces.type_aliases.keys()") equals `-1`
   - Expected: source.index_of("surfaces.constants.keys()") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the aligned arrays in the module lowering lookup")
val source = read_file_text(MODULE_LOWERING)
expect(source.index_of("val names = surfaces.index_by_name.keys()")).to_equal(-1)
expect(source.index_of("val indices = surfaces.index_by_name.values()")).to_equal(-1)
expect(source.index_of("self.module_surfaces.index_by_name.keys()")).to_equal(-1)
expect(source.index_of("surfaces.composites.keys()")).to_equal(-1)
expect(source.index_of("surfaces.enums.keys()")).to_equal(-1)
expect(source.index_of("surfaces.traits.keys()")).to_equal(-1)
expect(source.index_of("surfaces.callables.keys()")).to_equal(-1)
expect(source.index_of("surfaces.type_aliases.keys()")).to_equal(-1)
expect(source.index_of("surfaces.constants.keys()")).to_equal(-1)
expect(source).to_contain("val names = surfaces.ordered_names")
expect(source).to_contain("val indices = surfaces.ordered_indices")
expect(source).to_contain("for sibling_name in self.module_surfaces.ordered_names")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/module_surface_index_allocation_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module surface scalar index allocation guard.
- module surface scalar index allocation guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `bff1bd395a8f7e8521939844efd2d9e933432a1eccb0652c0f26d6ef45e36fe4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bff1bd395a8f7e8521939844efd2d9e933432a1eccb0652c0f26d6ef45e36fe4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bff1bd395a8f7e8521939844efd2d9e933432a1eccb0652c0f26d6ef45e36fe4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/hir/module_surface_index_allocation_guard_spec.spl
mirror: doc/06_spec/unit/compiler/hir/module_surface_index_allocation_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/module_surface_index_allocation_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/module_surface_index_allocation_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/module_surface_index_allocation_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/hir/module_surface_index_allocation_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not rebuild Dict key/value arrays in module surface lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/module_surface_index_allocation_guard_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the aligned arrays in the module lowering lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
