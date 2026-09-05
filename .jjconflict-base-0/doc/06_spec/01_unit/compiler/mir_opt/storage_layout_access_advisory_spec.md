# Storage Layout Access Advisory Specification

> Tests covering typed storage access layout advisory.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Layout Access Advisory Specification

## Scenarios

### typed storage access layout advisory

#### advises SoA SIMD AoSoA explicit GPU grouping and pinned ABI

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- advises SoA SIMD AoSoA explicit GPU grouping and pinned ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advises SoA SIMD AoSoA explicit GPU grouping and pinned ABI")
val function = advisory_function(false, false)
assert_equal(advisory_layout_tag(function, 1, false, false),
    storage_layout_kind_to_u8(StorageLayoutKind.SoA))
assert_equal(advisory_layout_tag(function, 8, false, false),
    storage_layout_kind_to_u8(StorageLayoutKind.AoSoA))
assert_equal(advisory_layout_tag(function, 1, true, false),
    storage_layout_kind_to_u8(StorageLayoutKind.Grouped))
assert_equal(advisory_layout_tag(function, 1, true, true),
    storage_layout_kind_to_u8(StorageLayoutKind.ExternalFixed))
```

</details>

#### falls back to AoS for dynamic unknown and empty evidence

- falls back to AoS for dynamic unknown and empty evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to AoS for dynamic unknown and empty evidence")
val dynamic = advisory_for(advisory_function(false, true), 1, false, false)
assert_false(dynamic.complete)
assert_false(dynamic.independent_field_access)
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(dynamic.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.AoS))

val unknown_summary = analyze_mir_storage_access_summary(
    advisory_function(false, false), [])
val unknown = storage_layout_access_advisory_v1(unknown_summary,
    9201, 3, 32, 16, 1, false, false, "access-policy-v1")
assert_false(unknown.complete)
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(unknown.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.AoS))

val empty_function = MirFunction(..advisory_function(false, false),
    blocks: [MirBlock(id: BlockId.new(0), label: Some("entry"),
        instructions: [], terminator: MirTerminator.Ret(nil))])
val empty = advisory_for(empty_function, 1, false, false)
assert_false(empty.complete)
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(empty.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.AoS))

val observed_function = MirFunction(..advisory_function(false, false),
    blocks: [MirBlock(id: BlockId.new(0), label: Some("entry"),
        instructions: [MirInst(kind: MirInstKind.Cast(
            LocalId(id: 50), advisory_copy(10), MirType.i64()), span: nil)],
        terminator: MirTerminator.Ret(nil))])
val observed = advisory_for(observed_function, 1, false, false)
assert_false(observed.complete)
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(observed.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.AoS))
```

</details>

#### keeps co-accessing field paths conflicting and identity order stable

- keeps co-accessing field paths conflicting and identity order stable


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps co-accessing field paths conflicting and identity order stable")
val forward_summary = analyze_mir_storage_access_summary(
    advisory_function(false, false),
    [mir_storage_region_binding_v1(10, 200)])
assert_false(parallel_access_paths_conflict(
    forward_summary.accesses[1], forward_summary.accesses[3]))
val forward = storage_layout_access_advisory_v1(forward_summary,
    9201, 3, 32, 16, 1, false, false, "access-policy-v1")
val reversed = advisory_for(advisory_function(true, false),
    1, false, false)
assert_true(forward.complete)
assert_equal(forward.identity, reversed.identity)

val coaccess_function = MirFunction(..advisory_function(false, false),
    blocks: [MirBlock(id: BlockId.new(0), label: Some("entry"),
        instructions: [
            MirInst(kind: MirInstKind.GetField(
                LocalId(id: 1), advisory_copy(10), 4), span: nil),
            MirInst(kind: MirInstKind.SetField(
                advisory_copy(10), 7, advisory_copy(40)), span: nil)
        ], terminator: MirTerminator.Ret(nil))])
val coaccess_summary = analyze_mir_storage_access_summary(
    coaccess_function, [mir_storage_region_binding_v1(10, 200)])
assert_true(parallel_access_paths_conflict(
    coaccess_summary.accesses[0], coaccess_summary.accesses[1]))
val coaccess = storage_layout_access_advisory_v1(coaccess_summary,
    9201, 3, 32, 16, 1, false, false, "access-policy-v1")
assert_false(coaccess.complete)
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(coaccess.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.AoS))
```

</details>

#### denies all-field and non-field record uses

- denies all-field and non-field record uses


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies all-field and non-field record uses")
val clean_summary = analyze_mir_storage_access_summary(
    advisory_function(false, false),
    [mir_storage_region_binding_v1(10, 200)])
val all_fields = storage_layout_access_advisory_v1(clean_summary,
    9201, 2, 32, 16, 1, false, false, "access-policy-v1")
assert_false(all_fields.complete)
assert_false(all_fields.independent_field_access)
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(all_fields.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.AoS))

val base = advisory_function(false, false)
val block = base.blocks[0]
var instructions = block.instructions
val call_type = MirType(kind: MirTypeKind.FuncPtr(MirSignature(
    params: [MirType.i64()], return_type: MirType.unit(),
    is_variadic: false)))
instructions.push(MirInst(kind: MirInstKind.Call(nil,
    MirOperand(kind: MirOperandKind.Const(
        MirConstValue.Str("consume_record"), call_type)),
    [advisory_copy(2)]), span: nil))
val escaped_record = MirFunction(..base, blocks: [
    MirBlock(..block, instructions: instructions)
])
val escaped = advisory_for(escaped_record, 1, false, false)
assert_false(escaped.complete)
assert_false(escaped.independent_field_access)
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(escaped.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.AoS))
```

</details>

#### uses memory policy to pin observed storage and deny critical conversion

- uses memory policy to pin observed storage and deny critical conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses memory policy to pin observed storage and deny critical conversion")
val observed_function = MirFunction(..advisory_function(false, false),
    blocks: [MirBlock(id: BlockId.new(0), label: Some("entry"),
        instructions: [MirInst(kind: MirInstKind.Cast(
            LocalId(id: 50), advisory_copy(10), MirType.i64()), span: nil)],
        terminator: MirTerminator.Ret(nil))])
val observed_summary = analyze_mir_storage_access_summary(
    observed_function, [mir_storage_region_binding_v1(10, 200)])
val balanced = storage_layout_access_advisory_with_memory_policy_v1(
    observed_summary, 9201, 3, 32, 16, 8, true, false,
    "access-policy-v1", ResolvedMemoryPolicyV1.balanced())
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(balanced.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.ExternalFixed))

val clean_summary = analyze_mir_storage_access_summary(
    advisory_function(false, false), [mir_storage_region_binding_v1(10, 200)])
val critical = storage_layout_access_advisory_with_memory_policy_v1(
    clean_summary, 9201, 3, 32, 16, 8, true, false,
    "access-policy-v1", ResolvedMemoryPolicyV1.for_assurance(
        AssuranceStrictness.Critical))
assert_false(critical.independent_field_access)
assert_equal(storage_layout_kind_to_u8(
    storage_layout_plan_auto(critical.request).layout),
    storage_layout_kind_to_u8(StorageLayoutKind.AoS))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed storage access layout advisory.
- typed storage access layout advisory

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `820fabb9d077451764d340e468c6aeaace97de3504a1ae2797e9f0126ec70025`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `820fabb9d077451764d340e468c6aeaace97de3504a1ae2797e9f0126ec70025`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `820fabb9d077451764d340e468c6aeaace97de3504a1ae2797e9f0126ec70025`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advises SoA SIMD AoSoA explicit GPU grouping and pinned ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to AoS for dynamic unknown and empty evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps co-accessing field paths conflicting and identity order stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
