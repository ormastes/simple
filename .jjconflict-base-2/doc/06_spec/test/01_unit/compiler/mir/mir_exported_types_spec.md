# MIR Exported Type Lowering Specification

> Verifies that HIR classes and structs are materialized into `MirModule.types`, including export metadata, field offsets, and explicit bit-width metadata.

<!-- sdn-diagram:id=mir_exported_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_exported_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_exported_types_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_exported_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR Exported Type Lowering Specification

Verifies that HIR classes and structs are materialized into `MirModule.types`, including export metadata, field offsets, and explicit bit-width metadata.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR #SFFI-MIR-TYPES |
| Category | Compiler / MIR |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/compiler/mir/mir_exported_types_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that HIR classes and structs are materialized into `MirModule.types`,
including export metadata, field offsets, and explicit bit-width metadata.

## Scenarios

### MIR exported type lowering

#### materializes exported classes into MirModule.types with bit metadata

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hir_module = make_module()
val lowering = MirLowering.new(hir_module.symbols)

val mir_module = lowering.lower_module(hir_module)
val type_def = mir_module.types[SymbolId(id: 10)]

expect(type_def.is_export_c).to_equal(true)
expect(type_def.name).to_equal("GpioRegister")

match type_def.kind:
    case Struct(fields):
        expect(fields.len()).to_equal(4)
        expect(fields[0].name).to_equal("mode")
        expect(fields[0].has_bits_attr).to_equal(true)
        expect(fields[0].bits_width).to_equal(4)
        expect(fields[0].offset).to_equal(0)
        expect(fields[3].bits_width).to_equal(2)
        expect(fields[3].offset).to_equal(0)
    case _:
        fail("exported GPIO register type did not lower to Struct fields")
```

</details>

#### materializes plain structs into MirModule.types with computed offsets

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hir_module = make_module()
val lowering = MirLowering.new(hir_module.symbols)

val mir_module = lowering.lower_module(hir_module)
val type_def = mir_module.types[SymbolId(id: 20)]

expect(type_def.is_export_c).to_equal(false)
expect(type_def.name).to_equal("Point")

match type_def.kind:
    case Struct(fields):
        expect(fields.len()).to_equal(2)
        expect(fields[0].offset).to_equal(0)
        expect(fields[1].offset).to_equal(4)
    case _:
        fail("plain Point type did not lower to Struct fields")
```

</details>

#### propagates driver manifest attributes onto MIR functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hir_module = make_module()
val lowering = MirLowering.new(hir_module.symbols)

val mir_module = lowering.lower_module(hir_module)
val fn_ = mir_module.functions[SymbolId(id: 30)]

expect(fn_.has_driver_manifest_attr).to_equal(true)
expect(fn_.driver_manifest_attr.kind).to_equal(DriverManifestAttrKind.Driver)
expect(fn_.driver_manifest_attr.version).to_equal("0.1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
