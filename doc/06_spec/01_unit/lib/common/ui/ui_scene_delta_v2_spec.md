# Ui Scene Delta V2 Specification

> Tests covering SceneDeltaRef (F3 completion, T5).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Scene Delta V2 Specification

## Scenarios

### SceneDeltaRef (F3 completion, T5)

#### round-trips dirty ranges through the v3 port

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips dirty ranges through the v3 port


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips dirty ranges through the v3 port")
val a = make_arena()
val p = a.lease_partition(1, 0, 2)
assert_true(ui_scene_v2_write_row(a, p, 0, [10, 11, 12, 13]) == 0)
assert_true(ui_scene_v2_write_row(a, p, 1, [20, 21, 22, 23]) == 0)
val delta = ui_scene_v3_build_delta(a)
# table 0 dirty -> bit 0 set, table 1 untouched -> bit 1 clear
assert_true((delta.changed_table_mask & 1u32) == 1u32)
assert_true((delta.changed_table_mask & 2u32) == 0u32)
assert_true(delta.dirty_range_start == 0u32)
assert_true(delta.dirty_range_count == 2u32)
# damage mirrors dirty until occlusion narrows it (documented in
# ui_scene_ports_v3.spl)
assert_true(delta.damage_start == delta.dirty_range_start)
assert_true(delta.damage_count == delta.dirty_range_count)
assert_true(delta.scene_generation == a.back_generation)
```

</details>

#### reflects a second producer's dirty rows in the same generation

- reflects a second producer's dirty rows in the same generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reflects a second producer's dirty rows in the same generation")
val a = make_arena()
val p0 = a.lease_partition(1, 0, 2)
assert_true(ui_scene_v2_write_row(a, p0, 0, [1, 2, 3, 4]) == 0)
val p1 = a.lease_partition(2, 1, 2)
assert_true(ui_scene_v2_write_row(a, p1, 0, [5, 6]) == 0)
val delta = ui_scene_v3_build_delta(a)
assert_true((delta.changed_table_mask & 1u32) == 1u32)
assert_true((delta.changed_table_mask & 2u32) == 2u32)
```

</details>

#### accepts a delta that strictly advances the cursor's generation

- accepts a delta that strictly advances the cursor's generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a delta that strictly advances the cursor's generation")
val cursor = SceneDeltaCursor.create()
val d1 = scene_delta_ref_make(1u32, 1u32, 0u32, 1u32, 0u32, 1u32)
assert_true(cursor.accept(d1) == SCENE_DELTA_V2_OK)
assert_true(cursor.last_seen_generation == 1u32)
val d2 = scene_delta_ref_make(3u32, 1u32, 1u32, 1u32, 1u32, 1u32)
assert_true(cursor.accept(d2) == SCENE_DELTA_V2_OK)
assert_true(cursor.last_seen_generation == 3u32)
```

</details>

#### refuses a stale (non-advancing) generation without mutating the cursor

- refuses a stale (non-advancing) generation without mutating the cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a stale (non-advancing) generation without mutating the cursor")
val cursor = SceneDeltaCursor.create()
val d1 = scene_delta_ref_make(5u32, 1u32, 0u32, 1u32, 0u32, 1u32)
assert_true(cursor.accept(d1) == SCENE_DELTA_V2_OK)
# same generation replayed
val stale_same = scene_delta_ref_make(5u32, 1u32, 0u32, 1u32, 0u32, 1u32)
assert_true(cursor.accept(stale_same) == SCENE_DELTA_V2_STALE_GENERATION)
assert_true(cursor.last_seen_generation == 5u32)
# older generation replayed
val stale_older = scene_delta_ref_make(2u32, 1u32, 0u32, 1u32, 0u32, 1u32)
assert_true(cursor.accept(stale_older) == SCENE_DELTA_V2_STALE_GENERATION)
assert_true(cursor.last_seen_generation == 5u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/ui_scene_delta_v2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SceneDeltaRef (F3 completion, T5).
- SceneDeltaRef (F3 completion, T5)

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

- Canonical SPipe generation for source `a935e43bc88c9f647c02b8831cee8447623bab91bce82c45de3393049c321fcc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a935e43bc88c9f647c02b8831cee8447623bab91bce82c45de3393049c321fcc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a935e43bc88c9f647c02b8831cee8447623bab91bce82c45de3393049c321fcc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/ui_scene_delta_v2_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/ui_scene_delta_v2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/ui_scene_delta_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/ui_scene_delta_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/ui_scene_delta_v2_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips dirty ranges through the v3 port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_delta_v2_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects a second producer's dirty rows in the same generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_delta_v2_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a delta that strictly advances the cursor's generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
