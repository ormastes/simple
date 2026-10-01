# Typed Storage View Declaration Specification

> Tests covering compiler-owned typed storage view declarations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Storage View Declaration Specification

## Scenarios

### compiler-owned typed storage view declarations

#### converts the allocation owner's fact without changing its identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts the allocation owner's fact without changing its identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts the allocation owner's fact without changing its identity")
var builder = MirBuilder.new()
val fact = builder.emit_typed_storage_alloc_owned_raw_v1(MirType.i64(),
    128, 9101, 4, 5, "allocation:9101:4:5:128",
    "compiler-site:particles:read_mass:0", "snapshot:abc123")
val template = declaration(MirTypedStorageBackingKindV1.CompilerOwnedRaw,
    StorageLayoutKind.SoA, 128, true, false, 8)
val converted = mir_typed_storage_view_declaration_from_allocation_v1(
    41, fact, 24, false, true, template.plan, template.fields)
assert_equal(converted.base_local_id, fact.base_local.id)
assert_equal(converted.allocation_identity, fact.allocation_identity)
assert_equal(converted.allocation_provenance, fact.allocation_provenance)
assert_equal(converted.source_revision, fact.source_revision)
```

</details>

#### admits exact private AoS and SoA allocations

- admits exact private AoS and SoA allocations


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits exact private AoS and SoA allocations")
for layout in [StorageLayoutKind.AoS, StorageLayoutKind.SoA]:
    val admitted = admit_mir_typed_storage_view_v1(declaration(
        MirTypedStorageBackingKindV1.CompilerOwnedRaw, layout, 128,
        true, false, 8))
    assert_true(admitted.ok)
    assert_equal(admitted.reason, "ok")
    assert_equal(admitted.allocation_provenance, "arena:task-7:allocation-2")
    assert_equal(admitted.source_revision, "snapshot:abc123")
    assert_true(admitted.site.?)
    assert_equal(admitted.site.unwrap().function_symbol_id, 41)
    assert_equal(admitted.site.unwrap().base_local_id, 3)
    assert_equal(admitted.site.unwrap().binding.revision, 4)
```

</details>

#### rejects RuntimeValue and external storage rather than relabeling it

- rejects RuntimeValue and external storage rather than relabeling it


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects RuntimeValue and external storage rather than relabeling it")
for backing in [MirTypedStorageBackingKindV1.RuntimeValueArray,
                MirTypedStorageBackingKindV1.ExternalPinned]:
    val rejected = admit_mir_typed_storage_view_v1(declaration(backing,
        StorageLayoutKind.SoA, 128, true, false, 8))
    assert_false(rejected.ok)
    assert_equal(rejected.reason,
        "storage-view-backing-not-compiler-owned-raw")
    assert_false(rejected.site.?)
```

</details>

#### fails closed for missing bounds allocation address and width evidence

- fails closed for missing bounds allocation address and width evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for missing bounds allocation address and width evidence")
val no_bounds = admit_mir_typed_storage_view_v1(declaration(
    MirTypedStorageBackingKindV1.CompilerOwnedRaw,
    StorageLayoutKind.SoA, 128, false, false, 8))
assert_equal(no_bounds.reason, "storage-view-index-bounds-unproven")
val too_small = admit_mir_typed_storage_view_v1(declaration(
    MirTypedStorageBackingKindV1.CompilerOwnedRaw,
    StorageLayoutKind.SoA, 64, true, false, 8))
assert_equal(too_small.reason,
    "storage-view-recipe:storage-view-allocation-too-small")
val observed = admit_mir_typed_storage_view_v1(declaration(
    MirTypedStorageBackingKindV1.CompilerOwnedRaw,
    StorageLayoutKind.AoS, 128, true, true, 8))
assert_equal(observed.reason,
    "storage-view-recipe:address-observed-or-abi-pinned")
val narrow = admit_mir_typed_storage_view_v1(declaration(
    MirTypedStorageBackingKindV1.CompilerOwnedRaw,
    StorageLayoutKind.AoS, 128, true, false, 4))
assert_equal(narrow.reason, "native-storage-field-width-unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compiler-owned typed storage view declarations.
- compiler-owned typed storage view declarations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `b1916d25e05f48a87ab92b6b282b23d0d4380170b77661a2d7af6867f0ce7a90`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1916d25e05f48a87ab92b6b282b23d0d4380170b77661a2d7af6867f0ce7a90`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1916d25e05f48a87ab92b6b282b23d0d4380170b77661a2d7af6867f0ce7a90`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts the allocation owner's fact without changing its identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits exact private AoS and SoA allocations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects RuntimeValue and external storage rather than relabeling it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
