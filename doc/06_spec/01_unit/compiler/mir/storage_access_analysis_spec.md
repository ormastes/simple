# Storage Access Analysis Specification

> Tests covering MIR storage access analysis.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Access Analysis Specification

## Scenarios

### MIR storage access analysis

#### preserves constant element ranges and read write modes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves constant element ranges and read write modes


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves constant element ranges and read write modes")
val instructions = [
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 1), storage_copy(10), [storage_index(2)]), span: nil),
    MirInst(kind: MirInstKind.Load(LocalId(id: 2), storage_copy(1)), span: nil),
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 3), storage_copy(20), [storage_index(3)]), span: nil),
    MirInst(kind: MirInstKind.Store(storage_copy(3), storage_copy(2)), span: nil)
]
val bindings = [
    mir_storage_region_binding_v1(10, 100),
    mir_storage_region_binding_v1(20, 100)
]
val accesses = analyze_mir_storage_accesses(storage_test_function(instructions), bindings)
assert_equal(accesses.len(), 2)
assert_true(accesses[0].known_range)
assert_equal(accesses[0].start, 2)
assert_equal(accesses[0].end, 3)
assert_equal(accesses[0].projection, "index:2")
assert_equal(parallel_access_mode_to_u8(accesses[0].mode), 0)
assert_equal(parallel_access_mode_to_u8(accesses[1].mode), 1)
assert_false(parallel_access_paths_overlap(accesses[0], accesses[1]))
assert_false(parallel_access_paths_conflict(accesses[0], accesses[1]))
```

</details>

#### collapses dynamic and unbound accesses conservatively

- collapses dynamic and unbound accesses conservatively


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collapses dynamic and unbound accesses conservatively")
val instructions = [
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 1), storage_copy(10), [storage_copy(30)]), span: nil),
    MirInst(kind: MirInstKind.Load(LocalId(id: 2), storage_copy(1)), span: nil),
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 3), storage_copy(20), [storage_copy(31)]), span: nil),
    MirInst(kind: MirInstKind.Store(storage_copy(3), storage_copy(2)), span: nil),
    MirInst(kind: MirInstKind.Load(LocalId(id: 4), storage_copy(99)), span: nil)
]
val bindings = [
    mir_storage_region_binding_v1(10, 100),
    mir_storage_region_binding_v1(20, 100)
]
val accesses = analyze_mir_storage_accesses(storage_test_function(instructions), bindings)
assert_equal(accesses.len(), 3)
assert_false(accesses[0].known_range)
assert_false(accesses[1].known_range)
assert_true(parallel_access_paths_conflict(accesses[0], accesses[1]))
assert_equal(accesses[2].region_id, MIR_STORAGE_UNKNOWN_REGION_ID)
assert_false(accesses[2].known_range)
```

</details>

#### records field paths without inventing field disjointness

- records field paths without inventing field disjointness


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records field paths without inventing field disjointness")
val instructions = [
    MirInst(kind: MirInstKind.GetField(
        LocalId(id: 1), storage_copy(10), 4), span: nil),
    MirInst(kind: MirInstKind.SetField(
        storage_copy(10), 7, storage_copy(40)), span: nil)
]
val accesses = analyze_mir_storage_accesses(
    storage_test_function(instructions),
    [mir_storage_region_binding_v1(10, 100)])
assert_equal(accesses.len(), 2)
assert_equal(accesses[0].projection, "field:4")
assert_equal(accesses[1].projection, "field:7")
assert_false(accesses[0].known_range)
assert_false(accesses[1].known_range)
assert_true(parallel_access_paths_conflict(accesses[0], accesses[1]))
```

</details>

#### preserves proven element partitions through record field reads

- preserves proven element partitions through record field reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves proven element partitions through record field reads")
val instructions = [
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 1), storage_copy(10), [storage_index(2)]), span: nil),
    MirInst(kind: MirInstKind.Load(
        LocalId(id: 2), storage_copy(1)), span: nil),
    MirInst(kind: MirInstKind.GetField(
        LocalId(id: 3), storage_copy(2), 4), span: nil),
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 4), storage_copy(10), [storage_index(5)]), span: nil),
    MirInst(kind: MirInstKind.Load(
        LocalId(id: 5), storage_copy(4)), span: nil),
    MirInst(kind: MirInstKind.GetField(
        LocalId(id: 6), storage_copy(5), 7), span: nil)
]
val accesses = analyze_mir_storage_accesses(
    storage_test_function(instructions),
    [mir_storage_region_binding_v1(10, 100)])
assert_equal(accesses.len(), 4)
assert_true(accesses[1].known_range)
assert_equal(accesses[1].start, 2)
assert_equal(accesses[1].end, 3)
assert_equal(accesses[1].projection, "index:2.field:4")
assert_true(accesses[3].known_range)
assert_equal(accesses[3].projection, "index:5.field:7")
assert_false(parallel_access_paths_conflict(accesses[1], accesses[3]))
```

</details>

#### fails closed when an owned address escapes but admits exact finalization

- fails closed when an owned address escapes but admits exact finalization


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when an owned address escapes but admits exact finalization")
val escaped = storage_test_function([
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 1), storage_copy(10), [storage_index(2)]), span: nil),
    MirInst(kind: MirInstKind.Call(nil, storage_function("unknown_consumer"),
        [storage_copy(1)]), span: nil)
])
val escaped_summary = analyze_mir_storage_access_summary(
    escaped, [mir_storage_region_binding_v1(10, 100)])
assert_true(escaped_summary.address_observed)
assert_true(escaped_summary.unknown_access)

val finalized = storage_test_function([
    MirInst(kind: MirInstKind.Call(nil, storage_function("rt_free"),
        [storage_copy(10)]), span: nil)
])
val finalized_summary = analyze_mir_storage_access_summary(
    finalized, [mir_storage_region_binding_v1(10, 100)])
assert_false(finalized_summary.address_observed)
assert_false(finalized_summary.unknown_access)
```

</details>

#### rejects ambiguous bindings and nested range claims

- rejects ambiguous bindings and nested range claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects ambiguous bindings and nested range claims")
val duplicate = [
    mir_storage_region_binding_v1(10, 100),
    mir_storage_region_binding_v1(10, 200)
]
assert_false(mir_storage_bindings_well_formed(duplicate))
assert_equal(analyze_mir_storage_accesses(storage_test_function([]), duplicate).len(), 0)

val nested = [
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 1), storage_copy(10), [storage_index(2)]), span: nil),
    MirInst(kind: MirInstKind.GetElementPtr(
        LocalId(id: 2), storage_copy(1), [storage_index(3)]), span: nil),
    MirInst(kind: MirInstKind.Load(LocalId(id: 3), storage_copy(2)), span: nil)
]
val accesses = analyze_mir_storage_accesses(
    storage_test_function(nested),
    [mir_storage_region_binding_v1(10, 100)])
assert_equal(accesses.len(), 1)
assert_false(accesses[0].known_range)
assert_equal(accesses[0].projection, "index:*")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/storage_access_analysis_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR storage access analysis.
- MIR storage access analysis

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `b8287fd3bb9298eff4c1b9a428ba737c624fece4ea6e12743d35d052aeef9f19`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8287fd3bb9298eff4c1b9a428ba737c624fece4ea6e12743d35d052aeef9f19`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8287fd3bb9298eff4c1b9a428ba737c624fece4ea6e12743d35d052aeef9f19`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/storage_access_analysis_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/storage_access_analysis_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/storage_access_analysis_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/storage_access_analysis_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/storage_access_analysis_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves constant element ranges and read write modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/storage_access_analysis_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses dynamic and unbound accesses conservatively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/storage_access_analysis_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records field paths without inventing field disjointness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
