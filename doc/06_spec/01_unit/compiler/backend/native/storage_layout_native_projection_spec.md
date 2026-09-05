# Storage Layout Native Projection Specification

> Tests covering typed host AoS and SoA native projection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Layout Native Projection Specification

## Scenarios

### typed host AoS and SoA native projection

#### automatically rewrites logical field projections with exact site bindings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- automatically rewrites logical field projections with exact site bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("automatically rewrites logical field projections with exact site bindings")
assert_rewritten_recipe(StorageLayoutKind.AoS, 16, 8)
assert_rewritten_recipe(StorageLayoutKind.SoA, 8, 320)
```

</details>

#### routes logical projections through the post-optimization native boundary

- routes logical projections through the post-optimization native boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes logical projections through the post-optimization native boundary")
val module = logical_projection_module(MirOperand.const_int(2))
val site = mir_storage_view_site_binding_v1(41, 0, true,
    projection_binding(StorageLayoutKind.SoA, false))
match compile_module_with_backend_target_cpu_storage_bindings(
    "native", module, false, 0, "", [site]):
    case Ok(compiled): assert_true(compiled.object_code != nil)
    case Err(_): assert_true(false)
match compile_module_with_backend_target_cpu_storage_bindings(
    "cranelift", module, false, 0, "", [site]):
    case Ok(_): assert_true(false)
    case Err(error):
        assert_true(error.message.contains(
            "typed storage projections require the custom native backend"))
```

</details>

#### fails closed on missing duplicate dynamic and observed bindings

- fails closed on missing duplicate dynamic and observed bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on missing duplicate dynamic and observed bindings")
val logical = logical_projection_module(MirOperand.const_int(2))
assert_equal(lower_mir_storage_project_fields_v1(logical, []).reason,
    "missing-storage-view-site-binding")
val site = mir_storage_view_site_binding_v1(41, 0, true,
    projection_binding(StorageLayoutKind.SoA, false))
assert_equal(lower_mir_storage_project_fields_v1(logical, [site, site]).reason,
    "duplicate-storage-view-site-binding")
val dynamic_field = logical_projection_module(MirOperand.copy(LocalId(id: 1)))
assert_equal(lower_mir_storage_project_fields_v1(dynamic_field, [site]).reason,
    "logical-projection-field-must-be-constant")
val observed = mir_storage_view_site_binding_v1(41, 0, true,
    projection_binding(StorageLayoutKind.SoA, true))
assert_equal(lower_mir_storage_project_fields_v1(logical, [observed]).reason,
    "storage-view-recipe:address-observed-or-abi-pinned")
val unproven = mir_storage_view_site_binding_v1(41, 0, false,
    projection_binding(StorageLayoutKind.SoA, false))
assert_equal(lower_mir_storage_project_fields_v1(logical, [unproven]).reason,
    "storage-view-index-bounds-unproven")
```

</details>

#### leaves the entire input MIR logical when a later site fails

- leaves the entire input MIR logical when a later site fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the entire input MIR logical when a later site fails")
val module = atomic_failure_module()
val site = mir_storage_view_site_binding_v1(41, 0, true,
    projection_binding(StorageLayoutKind.SoA, false))
val result = lower_mir_storage_project_fields_v1(module, [site])
assert_false(result.ok)
assert_equal(result.reason, "missing-storage-view-site-binding")
assert_logical_projection_name(module.functions[SymbolId.new(41)].blocks[0].instructions[0])
assert_logical_projection_name(module.functions[SymbolId.new(41)].blocks[0].instructions[1])
```

</details>

#### rejects a binding whose allocation cannot contain the projection

- rejects a binding whose allocation cannot contain the projection


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a binding whose allocation cannot contain the projection")
val too_small = mir_storage_view_binding_v1(7001, 9, 64, 64, 16, false,
    projection_plan(StorageLayoutKind.SoA), [
        mir_storage_field_binding_v1(0, 0, 8, 32)
    ])
assert_equal(mir_storage_address_recipe_v1(too_small, 0).reason,
    "storage-view-allocation-too-small")
```

</details>

#### rejects non-pointer-width fields until typed memory operations land

- rejects non-pointer-width fields until typed memory operations land


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-pointer-width fields until typed memory operations land")
val logical = logical_projection_module(MirOperand.const_int(1))
val site = mir_storage_view_site_binding_v1(41, 0, true,
    projection_binding(StorageLayoutKind.SoA, false))
assert_equal(lower_mir_storage_project_fields_v1(logical, [site]).reason,
    "native-storage-field-width-unsupported")
```

</details>

#### matches canonical projection for unequal fields and runtime indices

- matches canonical projection for unequal fields and runtime indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches canonical projection for unequal fields and runtime indices")
for layout in [StorageLayoutKind.AoS, StorageLayoutKind.SoA]:
    val binding = projection_binding(layout, false)
    for field_id in 0..3:
        val recipe = mir_storage_address_recipe_v1(binding, field_id)
        assert_true(recipe.ok)
        for index in 0..64:
            val field = binding.fields[field_id]
            val expected = storage_layout_project(binding.plan,
                storage_projection_request_v1(index, binding.element_count,
                    field.logical_offset, field.field_size,
                    binding.logical_stride, field.column_offset, 0, 0))
            assert_true(expected.ok)
            assert_equal(recipe.base_offset + index * recipe.scale,
                expected.byte_offset)
```

</details>

#### lowers the affine recipe through real native machine selection

- lowers the affine recipe through real native machine selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers the affine recipe through real native machine selection")
val recipe = mir_storage_address_recipe_v1(
    projection_binding(StorageLayoutKind.SoA, false), 2)
val selected = isel_module(
    projection_intrinsic_module(recipe.scale, recipe.base_offset))
var saw_mul = false
var saw_add = false
var saw_base_offset = false
for block in selected.functions[0].blocks:
    for instruction in block.insts:
        if instruction.opcode == X86_OP_IMUL: saw_mul = true
        if instruction.opcode == X86_OP_ADD: saw_add = true
        if instruction.opcode == X86_OP_ADD_IMM: saw_base_offset = true
        assert_false(instruction.opcode == X86_OP_NOP)
assert_true(saw_mul and saw_add and saw_base_offset)
```

</details>

#### materializes base offsets that exceed signed ADD immediate width

- materializes base offsets that exceed signed ADD immediate width


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("materializes base offsets that exceed signed ADD immediate width")
val selected = isel_module(projection_intrinsic_module(8, 2147483648))
var saw_offset_register = false
var saw_immediate_add = false
for block in selected.functions[0].blocks:
    for instruction in block.insts:
        if instruction.opcode == X86_OP_MOV_REG_IMM:
            saw_offset_register = true
        if instruction.opcode == X86_OP_ADD_IMM:
            saw_immediate_add = true
assert_true(saw_offset_register)
assert_false(saw_immediate_add)
```

</details>

#### rejects observed ABI and unsupported physical layouts

- rejects observed ABI and unsupported physical layouts


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects observed ABI and unsupported physical layouts")
val observed = mir_storage_address_recipe_v1(
    projection_binding(StorageLayoutKind.SoA, true), 1)
assert_false(observed.ok)
assert_equal(observed.reason, "address-observed-or-abi-pinned")
val grouped = mir_storage_address_recipe_v1(
    projection_binding(StorageLayoutKind.Grouped, false), 1)
assert_false(grouped.ok)
assert_equal(grouped.reason, "layout-requires-specialized-lowering")
assert_equal(mir_storage_address_recipe_v1(
    projection_binding(StorageLayoutKind.AoS, false), 99).reason,
    "unknown-field")
```

</details>

#### rejects overlapping SoA columns across the whole bound schema

- rejects overlapping SoA columns across the whole bound schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlapping SoA columns across the whole bound schema")
val malformed = mir_storage_view_binding_v1(7001, 9, 64, 1024, 16, false,
    projection_plan(StorageLayoutKind.SoA), [
        mir_storage_field_binding_v1(0, 0, 4, 0),
        mir_storage_field_binding_v1(1, 8, 8, 128)
    ])
assert_equal(mir_storage_address_recipe_v1(malformed, 0).reason,
    "overlapping-physical-columns")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed host AoS and SoA native projection.
- typed host AoS and SoA native projection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `258715df626b9ccfc68589bcc845db21d388d3dada0ec52227d710bae1bbc8a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `258715df626b9ccfc68589bcc845db21d388d3dada0ec52227d710bae1bbc8a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `258715df626b9ccfc68589bcc845db21d388d3dada0ec52227d710bae1bbc8a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/native/storage_layout_native_projection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/native/storage_layout_native_projection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/native/storage_layout_native_projection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'automatically rewrites logical field projections with exact site bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes logical projections through the post-optimization native boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on missing duplicate dynamic and observed bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
