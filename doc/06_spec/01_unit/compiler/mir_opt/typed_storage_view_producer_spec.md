# Typed Storage View Producer Specification

> Tests covering automatic compiler-owned typed storage producer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Storage View Producer Specification

## Scenarios

### automatic compiler-owned typed storage producer

#### replaces the canonical record chain and retains the value load

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- replaces the canonical record chain and retains the value load


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces the canonical record chain and retains the value load")
val original = producer_module(true, 3, false)
val produced = produce_mir_typed_storage_views_v1(original,
    [producer_declaration(StorageLayoutKind.SoA)])
assert_true(produced.ok)
assert_equal(produced.produced_count, 1)
assert_equal(produced.sites.len(), 1)
assert_equal(produced.evidence.len(), 1)
assert_equal(produced.evidence[0].allocation_provenance,
    "arena:task-9:allocation-1")
assert_equal(count_intrinsic(original, MIR_STORAGE_PROJECT_FIELD_V1), 0)
assert_equal(count_intrinsic(produced.module, MIR_STORAGE_PROJECT_FIELD_V1), 1)
val instructions = produced.module.functions[SymbolId.new(41)].blocks[0].instructions
match instructions[instructions.len() - 2].kind:
    case Intrinsic(Some(dest), name, args):
        assert_equal(dest.id, 2)
        assert_equal(name, MIR_STORAGE_PROJECT_FIELD_V1)
        assert_equal(args.len(), 3)
    case _: assert_true(false)
match instructions[instructions.len() - 1].kind:
    case Load(dest, ptr):
        assert_equal(dest.id, 4)
        match ptr.kind:
            case Copy(local): assert_equal(local.id, 2)
            case _: assert_true(false)
    case _: assert_true(false)
```

</details>

#### feeds the existing exact AoS and SoA late address rewrite

- feeds the existing exact AoS and SoA late address rewrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("feeds the existing exact AoS and SoA late address rewrite")
for layout in [StorageLayoutKind.AoS, StorageLayoutKind.SoA]:
    val produced = produce_mir_typed_storage_views_v1(
        producer_module(true, 3, false), [producer_declaration(layout)])
    val lowered = lower_mir_storage_project_fields_v1(
        produced.module, produced.sites)
    assert_true(lowered.ok)
    assert_equal(lowered.rewritten_count, 1)
    assert_equal(count_intrinsic(lowered.module,
        MIR_STORAGE_PROJECT_ADDRESS_V1), 1)
match compile_module_with_backend_target_cpu_storage_declarations(
    "native", producer_module(true, 3, false), false, 0, "",
    [producer_declaration(StorageLayoutKind.SoA)]):
    case Ok(compiled): assert_true(compiled.object_code != nil)
    case Err(_): assert_true(false)
```

</details>

#### rejects absent allocation proof out-of-range indices and escapes atomically

- rejects absent allocation proof out-of-range indices and escapes atomically


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects absent allocation proof out-of-range indices and escapes atomically")
val no_marker_input = producer_module(false, 3, false)
val no_marker = produce_mir_typed_storage_views_v1(no_marker_input,
    [producer_declaration(StorageLayoutKind.SoA)])
assert_false(no_marker.ok)
assert_equal(no_marker.reason, "storage-view-owned-raw-allocation-missing")
assert_equal(count_intrinsic(no_marker.module, MIR_STORAGE_PROJECT_FIELD_V1), 0)
val out_of_range = produce_mir_typed_storage_views_v1(
    producer_module(true, 5, false),
    [producer_declaration(StorageLayoutKind.SoA)])
assert_equal(out_of_range.reason, "storage-view-index-bounds-unproven")
val escaped = produce_mir_typed_storage_views_v1(
    producer_module(true, 3, true),
    [producer_declaration(StorageLayoutKind.SoA)])
assert_equal(escaped.reason, "storage-projection-temporary-escapes")
```

</details>

#### rejects unused declarations rather than emitting stale evidence

- rejects unused declarations rather than emitting stale evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unused declarations rather than emitting stale evidence")
val empty = producer_module(true, 3, false)
val declaration = mir_typed_storage_view_declaration_v1(99, 0, 9201,
    "arena:other", "allocation:other", "snapshot:other", 4,
    MirTypedStorageBackingKindV1.CompilerOwnedRaw, 5, 128, 24, false,
    true, producer_declaration(StorageLayoutKind.AoS).plan,
    producer_declaration(StorageLayoutKind.AoS).fields)
val result = produce_mir_typed_storage_views_v1(empty, [declaration])
assert_false(result.ok)
assert_equal(result.reason, "stale-typed-storage-declaration")
assert_equal(result.sites.len(), 0)
```

</details>

#### derives address escape gating and permits the exact owner finalizer

- derives address escape gating and permits the exact owner finalizer


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives address escape gating and permits the exact owner finalizer")
val escaped = produce_mir_typed_storage_views_v1(
    producer_module_with_owner_call("unknown_consumer"),
    [producer_declaration(StorageLayoutKind.SoA)])
assert_false(escaped.ok)
assert_equal(escaped.reason, "storage-view-address-observed")
assert_equal(count_intrinsic(escaped.module,
    MIR_STORAGE_PROJECT_FIELD_V1), 0)

val finalized = produce_mir_typed_storage_views_v1(
    producer_module_with_owner_call("rt_free"),
    [producer_declaration(StorageLayoutKind.SoA)])
assert_true(finalized.ok)
assert_equal(finalized.produced_count, 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering automatic compiler-owned typed storage producer.
- automatic compiler-owned typed storage producer

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

- Canonical SPipe generation for source `0e72d211249e1462e76852bdc5d300cac5e5eaf099067ab594d13c885bf571c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e72d211249e1462e76852bdc5d300cac5e5eaf099067ab594d13c885bf571c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e72d211249e1462e76852bdc5d300cac5e5eaf099067ab594d13c885bf571c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces the canonical record chain and retains the value load' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'feeds the existing exact AoS and SoA late address rewrite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects absent allocation proof out-of-range indices and escapes atomically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
