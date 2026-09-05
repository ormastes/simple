# MIR Exported Type Lowering Specification

> Verifies that HIR classes and structs are materialized into `MirModule.types`, including export metadata, field offsets, and explicit bit-width metadata.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that HIR classes and structs are materialized into `MirModule.types`,
including export metadata, field offsets, and explicit bit-width metadata.

## Scenarios

### MIR exported type lowering

#### materializes exported classes into MirModule.types with bit metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- materializes exported classes into MirModule.types with bit metadata
   - Expected: type_def.is_export_c is true
   - Expected: type_def.name equals `GpioRegister`
   - Expected: fields.len() equals `4`
   - Expected: fields[0].name equals `mode`
   - Expected: fields[0].has_bits_attr is true
   - Expected: fields[0].bits_width equals `4`
   - Expected: fields[0].offset equals `0`
   - Expected: fields[3].bits_width equals `2`
   - Expected: fields[3].offset equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("materializes exported classes into MirModule.types with bit metadata")
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

- materializes plain structs into MirModule.types with computed offsets
   - Expected: type_def.is_export_c is false
   - Expected: type_def.name equals `Point`
   - Expected: fields.len() equals `2`
   - Expected: fields[0].offset equals `0`
   - Expected: fields[1].offset equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("materializes plain structs into MirModule.types with computed offsets")
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

- propagates driver manifest attributes onto MIR functions
   - Expected: fn_.has_driver_manifest_attr is true
   - Expected: fn_.driver_manifest_attr.kind equals `DriverManifestAttrKind.Driver`
   - Expected: fn_.driver_manifest_attr.version equals `0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("propagates driver manifest attributes onto MIR functions")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db8f0055d4ca1ae66b30323c1887aef81d69551a22dd5977d33f62b3458911b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db8f0055d4ca1ae66b30323c1887aef81d69551a22dd5977d33f62b3458911b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db8f0055d4ca1ae66b30323c1887aef81d69551a22dd5977d33f62b3458911b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/mir_exported_types_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_exported_types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/mir_exported_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_exported_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_exported_types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/mir_exported_types_spec.spl:209:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes exported classes into MirModule.types with bit metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_exported_types_spec.spl:233:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes plain structs into MirModule.types with computed offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_exported_types_spec.spl:253:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates driver manifest attributes onto MIR functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
