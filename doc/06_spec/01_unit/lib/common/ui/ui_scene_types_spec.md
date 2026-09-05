# ui_scene_types_spec

> Purpose: Prove that UiSceneTableId numbering (design section 2.1, cross-module ABI).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ui_scene_types_spec

Purpose: Prove that UiSceneTableId numbering (design section 2.1, cross-module ABI).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/ui_scene_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that UiSceneTableId numbering (design section 2.1, cross-module ABI).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### UiSceneTableId numbering (design section 2.1, cross-module ABI)

#### should pin all 16 UiSceneTableId values exactly as design 2.1 numbers them

- Compare each named table id constant to its literal design number
   - Expected: UI_SCENE_TABLE_COMMANDS equals `0u16`
   - Expected: UI_SCENE_TABLE_GEOMETRY equals `1u16`
   - Expected: UI_SCENE_TABLE_PAINT equals `2u16`
   - Expected: UI_SCENE_TABLE_TEXT_RUNS equals `3u16`
   - Expected: UI_SCENE_TABLE_GLYPHS equals `4u16`
   - Expected: UI_SCENE_TABLE_RESOURCES equals `5u16`
   - Expected: UI_SCENE_TABLE_PATH_SPANS equals `6u16`
   - Expected: UI_SCENE_TABLE_PATH_POINTS equals `7u16`
   - Expected: UI_SCENE_TABLE_CLIPS equals `8u16`
   - Expected: UI_SCENE_TABLE_TRANSFORMS equals `9u16`
   - Expected: UI_SCENE_TABLE_HIT_SHAPES equals `10u16`
   - Expected: UI_SCENE_TABLE_PROVENANCE_EDGES equals `11u16`
   - Expected: UI_SCENE_TABLE_OWNER_RECORDS equals `12u16`
   - Expected: UI_SCENE_TABLE_ACTION_BINDINGS equals `13u16`
   - Expected: UI_SCENE_TABLE_PREPARED_BATCHES equals `14u16`
   - Expected: UI_SCENE_TABLE_DIRTY_RANGES equals `15u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-COMMON-001
step("Compare each named table id constant to its literal design number")
expect(UI_SCENE_TABLE_COMMANDS).to_equal(0u16)
expect(UI_SCENE_TABLE_GEOMETRY).to_equal(1u16)
expect(UI_SCENE_TABLE_PAINT).to_equal(2u16)
expect(UI_SCENE_TABLE_TEXT_RUNS).to_equal(3u16)
expect(UI_SCENE_TABLE_GLYPHS).to_equal(4u16)
expect(UI_SCENE_TABLE_RESOURCES).to_equal(5u16)
expect(UI_SCENE_TABLE_PATH_SPANS).to_equal(6u16)
expect(UI_SCENE_TABLE_PATH_POINTS).to_equal(7u16)
expect(UI_SCENE_TABLE_CLIPS).to_equal(8u16)
expect(UI_SCENE_TABLE_TRANSFORMS).to_equal(9u16)
expect(UI_SCENE_TABLE_HIT_SHAPES).to_equal(10u16)
expect(UI_SCENE_TABLE_PROVENANCE_EDGES).to_equal(11u16)
expect(UI_SCENE_TABLE_OWNER_RECORDS).to_equal(12u16)
expect(UI_SCENE_TABLE_ACTION_BINDINGS).to_equal(13u16)
expect(UI_SCENE_TABLE_PREPARED_BATCHES).to_equal(14u16)
expect(UI_SCENE_TABLE_DIRTY_RANGES).to_equal(15u16)
```

</details>

### Count -> scan -> verify state machine (design section 5)

#### should scan one table's producer counts into disjoint, gapless ranges

- should scan one table's producer counts into disjoint, gapless ranges
- Scan counts {3, 0, 5} for a single table
   - Expected: ranges.len() equals `3`
   - Expected: ranges[0].start equals `0u32`
   - Expected: ranges[0].count equals `3u32`
   - Expected: ranges[1].start equals `3u32`
   - Expected: ranges[1].count equals `0u32`
   - Expected: ranges[2].start equals `3u32`
   - Expected: ranges[2].count equals `5u32`
- Each range must start exactly where the previous one ended
   - Expected: ranges[1].start equals `ranges[0].start + ranges[0].count`
   - Expected: ranges[2].start equals `ranges[1].start + ranges[1].count`
   - Expected: ranges[2].start + ranges[2].count equals `8u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should scan one table's producer counts into disjoint, gapless ranges")
step("Scan counts {3, 0, 5} for a single table")
val ranges = ui_scene_scan_table([3u32, 0u32, 5u32])

expect(ranges.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(ranges[0].start).to_equal(0u32)
expect(ranges[0].count).to_equal(3u32)
expect(ranges[1].start).to_equal(3u32)
expect(ranges[1].count).to_equal(0u32)
expect(ranges[2].start).to_equal(3u32)
expect(ranges[2].count).to_equal(5u32)

step("Each range must start exactly where the previous one ended")
expect(ranges[1].start).to_equal(ranges[0].start + ranges[0].count)
expect(ranges[2].start).to_equal(ranges[1].start + ranges[1].count)
expect(ranges[2].start + ranges[2].count).to_equal(8u32)
```

</details>

#### should scan all 16 tables across multiple producers into disjoint per-producer ranges

- should scan all 16 tables across multiple producers into disjoint per-producer ranges
- Two producers each report a count for the COMMANDS table only
   - Expected: scanned.len() equals `2`
   - Expected: r0.start equals `0u32`
   - Expected: r0.count equals `2u32`
   - Expected: r1.start equals `2u32`
   - Expected: r1.count equals `3u32`
- An untouched table stays a zero-width range for both producers
   - Expected: g0.start equals `0u32`
   - Expected: g0.count equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should scan all 16 tables across multiple producers into disjoint per-producer ranges")
step("Two producers each report a count for the COMMANDS table only")
var c0 = ui_scene_counts_zero()
c0 = ui_scene_counts_set(c0, UI_SCENE_TABLE_COMMANDS, 2u32)
var c1 = ui_scene_counts_zero()
c1 = ui_scene_counts_set(c1, UI_SCENE_TABLE_COMMANDS, 3u32)

val scanned = ui_scene_scan([c0, c1])
expect(scanned.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement

val r0 = ui_scene_ranges_at(scanned[0], UI_SCENE_TABLE_COMMANDS)
val r1 = ui_scene_ranges_at(scanned[1], UI_SCENE_TABLE_COMMANDS)
expect(r0.start).to_equal(0u32)
expect(r0.count).to_equal(2u32)
expect(r1.start).to_equal(2u32)
expect(r1.count).to_equal(3u32)

step("An untouched table stays a zero-width range for both producers")
val g0 = ui_scene_ranges_at(scanned[0], UI_SCENE_TABLE_GEOMETRY)
expect(g0.start).to_equal(0u32)
expect(g0.count).to_equal(0u32)
```

</details>

#### should refuse with a receipt naming the exact table/required/capacity when required exceeds capacity, and pass nothing to emit

- should refuse with a receipt naming the exact table/required/capacity when required exceeds capacity, and pass nothing to emit
- A producer's GEOMETRY total (20) exceeds the reserved capacity (10)
   - Expected: receipt == nil is false
   - Expected: r.table_id equals `UI_SCENE_TABLE_GEOMETRY`
   - Expected: r.required equals `20u32`
   - Expected: r.capacity equals `10u32`
   - Expected: r.kind equals `UI_SCENE_OVERFLOW_CAPACITY`
   - Expected: r.producer_kind equals `UI_PRODUCER_WM`
   - Expected: r.producer_id equals `7u32`
   - Expected: r.snapshot_id equals `42u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should refuse with a receipt naming the exact table/required/capacity when required exceeds capacity, and pass nothing to emit")
step("A producer's GEOMETRY total (20) exceeds the reserved capacity (10)")
var totals = ui_scene_counts_zero()
totals = ui_scene_counts_set(totals, UI_SCENE_TABLE_GEOMETRY, 20u32)
var capacity = ui_scene_capacity_zero()
capacity = ui_scene_capacity_set(capacity, UI_SCENE_TABLE_GEOMETRY, 10u32)

val receipt = ui_scene_verify(totals, capacity, UI_PRODUCER_WM, 7u32, 42u64)
expect(receipt == nil).to_equal(false)
if val r = receipt:
    expect(r.table_id).to_equal(UI_SCENE_TABLE_GEOMETRY)
    expect(r.required).to_equal(20u32)
    expect(r.capacity).to_equal(10u32)
    expect(r.kind).to_equal(UI_SCENE_OVERFLOW_CAPACITY)
    expect(r.producer_kind).to_equal(UI_PRODUCER_WM)
    expect(r.producer_id).to_equal(7u32)
    expect(r.snapshot_id).to_equal(42u64)
```

</details>

#### should pass verify with no receipt when every table stays within capacity

- should pass verify with no receipt when every table stays within capacity
- A COMMANDS total of 4 is well inside a capacity of 100
   - Expected: receipt == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should pass verify with no receipt when every table stays within capacity")
step("A COMMANDS total of 4 is well inside a capacity of 100")
var totals = ui_scene_counts_zero()
totals = ui_scene_counts_set(totals, UI_SCENE_TABLE_COMMANDS, 4u32)
var capacity = ui_scene_capacity_zero()
capacity = ui_scene_capacity_set(capacity, UI_SCENE_TABLE_COMMANDS, 100u32)

val receipt = ui_scene_verify(totals, capacity, UI_PRODUCER_GUI, 1u32, 1u64)
expect(receipt == nil).to_equal(true)
```

</details>

### Owner/action table (design section 2.4)

#### should walk the owner-record parent chain from a leaf up to the WM root

- should walk the owner-record parent chain from a leaf up to the WM root
- Row 0's parent is row 1; row 1 is the WM root (NO_ID parent)
   - Expected: chain.len() equals `2`
   - Expected: chain[0] equals `0u32`
   - Expected: chain[1] equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should walk the owner-record parent chain from a leaf up to the WM root")
step("Row 0's parent is row 1; row 1 is the WM root (NO_ID parent)")
val owners = [
    UiOwnerRecord(
        producer_kind: UI_PRODUCER_GUI, event_policy: 0u16,
        semantic_id: 1u32, semantic_generation: 1u32,
        parent_owner_id: 1u32, action_binding_id: DRAW_IR_V3_NO_ID
    ),
    UiOwnerRecord(
        producer_kind: UI_PRODUCER_WM, event_policy: 0u16,
        semantic_id: 2u32, semantic_generation: 1u32,
        parent_owner_id: DRAW_IR_V3_NO_ID, action_binding_id: DRAW_IR_V3_NO_ID
    )
]

val chain = ui_scene_owner_chain(owners, 0u32)
expect(chain.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(chain[0]).to_equal(0u32)
expect(chain[1]).to_equal(1u32)
```

</details>

#### should return just the root when the root itself is walked

- should return just the root when the root itself is walked
- Verify: should return just the root when the root itself is walked
   - Expected: chain.len() equals `1`
   - Expected: chain[0] equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return just the root when the root itself is walked")
step("Verify: should return just the root when the root itself is walked")
val owners = [
    UiOwnerRecord(
        producer_kind: UI_PRODUCER_WM, event_policy: 0u16,
        semantic_id: 9u32, semantic_generation: 1u32,
        parent_owner_id: DRAW_IR_V3_NO_ID, action_binding_id: DRAW_IR_V3_NO_ID
    )
]
val chain = ui_scene_owner_chain(owners, 0u32)
expect(chain.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(chain[0]).to_equal(0u32)
```

</details>

#### should refuse dispatch on a stale app_generation and accept on a fresh one

- should refuse dispatch on a stale app_generation and accept on a fresh one
- Same binding checked against a stale, then the matching, app_generation
   - Expected: stale.accepted is false
   - Expected: stale.reason equals `UI_SCENE_DISPATCH_REFUSE_STALE_APP_GENERATION`
   - Expected: fresh.accepted is true
   - Expected: fresh.reason equals `UI_SCENE_DISPATCH_OK`
   - Expected: fresh.target_owner_id equals `3u32`
   - Expected: fresh.action_id equals `77u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should refuse dispatch on a stale app_generation and accept on a fresh one")
step("Same binding checked against a stale, then the matching, app_generation")
val binding = MenuActionBinding(
    app_id: 9u32, app_generation: 5u32, menu_revision: 2u32,
    action_id: 77u32, default_target_owner_id: 3u32
)

val stale = ui_scene_validate_menu_action_dispatch(binding, 6u32, 2u32)
expect(stale.accepted).to_equal(false)
expect(stale.reason).to_equal(UI_SCENE_DISPATCH_REFUSE_STALE_APP_GENERATION)

val fresh = ui_scene_validate_menu_action_dispatch(binding, 5u32, 2u32)
expect(fresh.accepted).to_equal(true)
expect(fresh.reason).to_equal(UI_SCENE_DISPATCH_OK)
expect(fresh.target_owner_id).to_equal(3u32)
expect(fresh.action_id).to_equal(77u32)
```

</details>

#### should also refuse dispatch on a stale menu_revision with a fresh app_generation

- should also refuse dispatch on a stale menu_revision with a fresh app_generation
- Verify: should also refuse dispatch on a stale menu_revision with a fresh app_generation
   - Expected: stale_menu.accepted is false
   - Expected: stale_menu.reason equals `UI_SCENE_DISPATCH_REFUSE_STALE_MENU_REVISION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should also refuse dispatch on a stale menu_revision with a fresh app_generation")
step("Verify: should also refuse dispatch on a stale menu_revision with a fresh app_generation")
val binding = MenuActionBinding(
    app_id: 9u32, app_generation: 5u32, menu_revision: 2u32,
    action_id: 77u32, default_target_owner_id: 3u32
)
val stale_menu = ui_scene_validate_menu_action_dispatch(binding, 5u32, 3u32)
expect(stale_menu.accepted).to_equal(false)
expect(stale_menu.reason).to_equal(UI_SCENE_DISPATCH_REFUSE_STALE_MENU_REVISION)
```

</details>

### Prepared2D sidecar (design section 2.5)

#### should compare Prepared2D cache keys equal only when all three fields match

- should compare Prepared2D cache keys equal only when all three fields match
- Verify: should compare Prepared2D cache keys equal only when all three fields match
   - Expected: ui_scene_prepared2d_cache_key_equal(key_a, key_b) is true
   - Expected: ui_scene_prepared2d_cache_key_equal(key_a, key_c) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should compare Prepared2D cache keys equal only when all three fields match")
step("Verify: should compare Prepared2D cache keys equal only when all three fields match")
val plan = Prepared2DPlan(
    batches: UiSceneRange(start: 0u32, count: 4u32),
    dirty_upload: UiSceneRange(start: 0u32, count: 1u32),
    damage_rect_count: 1u32, capability_key: 55u64, scene_generation: 9u32
)
val key_a = ui_scene_prepared2d_cache_key(plan, 1u32)
val key_b = ui_scene_prepared2d_cache_key(plan, 1u32)
val key_c = ui_scene_prepared2d_cache_key(plan, 2u32)

expect(ui_scene_prepared2d_cache_key_equal(key_a, key_b)).to_equal(true)
expect(ui_scene_prepared2d_cache_key_equal(key_a, key_c)).to_equal(false)
```

</details>

#### should read Prepared2DBatch.flags bit 0 as NEEDS_OFFSCREEN

- should read Prepared2DBatch.flags bit 0 as NEEDS_OFFSCREEN
- Verify: should read Prepared2DBatch.flags bit 0 as NEEDS_OFFSCREEN
   - Expected: ui_scene_prepared2d_batch_needs_offscreen(plain) is false
   - Expected: ui_scene_prepared2d_batch_needs_offscreen(offscreen) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should read Prepared2DBatch.flags bit 0 as NEEDS_OFFSCREEN")
step("Verify: should read Prepared2DBatch.flags bit 0 as NEEDS_OFFSCREEN")
val plain = Prepared2DBatch(
    first_command: 0u32, command_count: 1u32, target_surface_id: 0u32,
    pipeline_id: 0u32, resource_set_id: 0u32,
    resolved_clip_id: DRAW_IR_V3_NO_ID, resolved_transform_id: DRAW_IR_V3_NO_ID,
    flags: 0u32
)
val offscreen = Prepared2DBatch(
    first_command: 0u32, command_count: 1u32, target_surface_id: 0u32,
    pipeline_id: 0u32, resource_set_id: 0u32,
    resolved_clip_id: DRAW_IR_V3_NO_ID, resolved_transform_id: DRAW_IR_V3_NO_ID,
    flags: UI_SCENE_PREPARED2D_FLAG_NEEDS_OFFSCREEN
)

expect(ui_scene_prepared2d_batch_needs_offscreen(plain)).to_equal(false)
expect(ui_scene_prepared2d_batch_needs_offscreen(offscreen)).to_equal(true)
```

</details>

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
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68e812a5445be81e5d3abc27ed031857ffd143bc5579adb576e5569f222c15b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68e812a5445be81e5d3abc27ed031857ffd143bc5579adb576e5569f222c15b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68e812a5445be81e5d3abc27ed031857ffd143bc5579adb576e5569f222c15b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/ui_scene_types_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/ui_scene_types_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/ui_scene_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/ui_scene_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin all 16 UiSceneTableId values exactly as design 2.1 numbers them' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pin all 16 UiSceneTableId values exactly as design 2.1 numbers them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should scan one table's producer counts into disjoint, gapless ranges' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should scan one table's producer counts into disjoint, gapless ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:120:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should scan all 16 tables across multiple producers into disjoint per-producer ranges' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should scan all 16 tables across multiple producers into disjoint per-producer ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:144:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse with a receipt naming the exact table/required/capacity when required exceeds capacity, and pass nothing to emit' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass verify with no receipt when every table stays within capacity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_types_spec.spl:181:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should walk the owner-record parent chain from a leaf up to the WM root' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
