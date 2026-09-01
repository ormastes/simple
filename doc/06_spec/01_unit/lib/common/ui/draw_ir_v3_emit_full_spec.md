# draw_ir_v3_emit_full_spec

> Purpose: Prove that Stable component id allocation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# draw_ir_v3_emit_full_spec

Purpose: Prove that Stable component id allocation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Stable component id allocation.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Stable component id allocation

#### should auto-assign sequential ids only to items that did not set one

- Two blank items and one with an explicit id, base = 100
   - Expected: assigned.items[0].component_id equals `100u32`
   - Expected: assigned.items[1].component_id equals `999u32`
   - Expected: assigned.items[2].component_id equals `101u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-COMMON-001
step("Two blank items and one with an explicit id, base = 100")
var a = draw_ir_v3_full_item_blank()
var b = draw_ir_v3_full_item_blank()
b.component_id = 999u32
var c = draw_ir_v3_full_item_blank()
var request = draw_ir_v3_full_request_blank()
request.items = [a, b, c]
request.first_component_id = 100u32

val assigned = draw_ir_v3_full_assign_component_ids(request)
expect(assigned.items[0].component_id).to_equal(100u32)
expect(assigned.items[1].component_id).to_equal(999u32)
expect(assigned.items[2].component_id).to_equal(101u32)
```

</details>

### Full-schema exact-size emission (design section 5, all 16 tables)

#### should count exact per-table rows for the mixed fixture before any emission

- should count exact per-table rows for the mixed fixture before any emission
- COUNT is pure/repeatable: rect+text+path+image
   - Expected: counts.commands equals `4u32`
   - Expected: counts.geometry equals `2u32`
   - Expected: counts.paint equals `3u32`
   - Expected: counts.text_runs equals `1u32`
   - Expected: counts.glyphs equals `3u32`
   - Expected: counts.resources equals `1u32`
   - Expected: counts.path_spans equals `1u32`
   - Expected: counts.path_points equals `4u32`
   - Expected: counts.clips equals `1u32`
   - Expected: counts.transforms equals `1u32`
   - Expected: counts.hit_shapes equals `1u32`
   - Expected: counts.provenance_edges equals `1u32`
   - Expected: counts.owner_records equals `4u32`
   - Expected: counts.action_bindings equals `1u32`
   - Expected: counts.prepared_batches equals `1u32`
   - Expected: counts.dirty_ranges equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should count exact per-table rows for the mixed fixture before any emission")
step("COUNT is pure/repeatable: rect+text+path+image")
val counts = draw_ir_v3_emit_full_count(_fixture_request())
expect(counts.commands).to_equal(4u32)
expect(counts.geometry).to_equal(2u32)
expect(counts.paint).to_equal(3u32)
expect(counts.text_runs).to_equal(1u32)
expect(counts.glyphs).to_equal(3u32)
expect(counts.resources).to_equal(1u32)
expect(counts.path_spans).to_equal(1u32)
expect(counts.path_points).to_equal(4u32)
expect(counts.clips).to_equal(1u32)
expect(counts.transforms).to_equal(1u32)
expect(counts.hit_shapes).to_equal(1u32)
expect(counts.provenance_edges).to_equal(1u32)
expect(counts.owner_records).to_equal(4u32)
expect(counts.action_bindings).to_equal(1u32)
expect(counts.prepared_batches).to_equal(1u32)
expect(counts.dirty_ranges).to_equal(1u32)
```

</details>

#### should emit exactly the counted rows into every one of the 16 tables

- should emit exactly the counted rows into every one of the 16 tables
- Run the full COUNT -> SCAN -> VERIFY -> EMIT pipeline
   - Expected: outcome.emitted is true
   - Expected: scene.commands.len() equals `4`
   - Expected: scene.geometry.xs.len() equals `2`
   - Expected: scene.paint.fill_colors.len() equals `3`
   - Expected: scene.text_runs.run_glyph_starts.len() equals `1`
   - Expected: scene.text_runs.glyph_ids.len() equals `3`
   - Expected: scene.resources.kinds.len() equals `1`
   - Expected: scene.path_points.span_point_starts.len() equals `1`
   - Expected: scene.path_points.point_xs.len() equals `4`
   - Expected: scene.clips.xs.len() equals `1`
   - Expected: scene.transforms.m11s.len() equals `1`
   - Expected: scene.hit_shapes.xs.len() equals `1`
   - Expected: scene.provenance.command_indices.len() equals `1`
   - Expected: outcome.owners.len() equals `4`
   - Expected: outcome.actions.len() equals `1`
   - Expected: outcome.prepared_batches.len() equals `1`
   - Expected: outcome.dirty_ranges.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should emit exactly the counted rows into every one of the 16 tables")
step("Run the full COUNT -> SCAN -> VERIFY -> EMIT pipeline")
val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 1u32, 1u32, 42u64,
    UI_PRODUCER_GUI, 1u32
)
expect(outcome.emitted).to_equal(true)
val scene = outcome.scene
expect(scene.commands.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(scene.geometry.xs.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(scene.paint.fill_colors.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(scene.text_runs.run_glyph_starts.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(scene.text_runs.glyph_ids.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(scene.resources.kinds.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(scene.path_points.span_point_starts.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(scene.path_points.point_xs.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(scene.clips.xs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(scene.transforms.m11s.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(scene.hit_shapes.xs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(scene.provenance.command_indices.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(outcome.owners.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(outcome.actions.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(outcome.prepared_batches.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(outcome.dirty_ranges.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### should leave geometry_id/paint_id/etc as NO_ID on a command whose item did not request that table

- should leave geometry_id/paint_id/etc as NO_ID on a command whose item did not request that table
- The TEXT item requests no geometry/paint/clip/transform/hit_shape
   - Expected: text_cmd.geometry_id equals `DRAW_IR_V3_NO_ID`
   - Expected: text_cmd.clip_id equals `DRAW_IR_V3_NO_ID`
   - Expected: text_cmd.transform_id equals `DRAW_IR_V3_NO_ID`
   - Expected: text_cmd.hit_shape_id equals `DRAW_IR_V3_NO_ID`
   - Expected: text_cmd.text_run_id equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should leave geometry_id/paint_id/etc as NO_ID on a command whose item did not request that table")
step("The TEXT item requests no geometry/paint/clip/transform/hit_shape")
val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 1u32, 1u32, 42u64,
    UI_PRODUCER_GUI, 1u32
)
val text_cmd = outcome.scene.commands[1]
expect(text_cmd.geometry_id).to_equal(DRAW_IR_V3_NO_ID)
expect(text_cmd.clip_id).to_equal(DRAW_IR_V3_NO_ID)
expect(text_cmd.transform_id).to_equal(DRAW_IR_V3_NO_ID)
expect(text_cmd.hit_shape_id).to_equal(DRAW_IR_V3_NO_ID)
expect(text_cmd.text_run_id).to_equal(0u32)
```

</details>

#### should write multiple glyphs into a contiguous span with the run's own start/count

- should write multiple glyphs into a contiguous span with the run's own start/count
- Verify: should write multiple glyphs into a contiguous span with the run's own start/count
   - Expected: outcome.scene.text_runs.run_glyph_starts[0] equals `0u32`
   - Expected: outcome.scene.text_runs.run_glyph_counts[0] equals `3u32`
   - Expected: outcome.scene.text_runs.glyph_ids[0] equals `1u32`
   - Expected: outcome.scene.text_runs.glyph_ids[2] equals `3u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should write multiple glyphs into a contiguous span with the run's own start/count")
step("Verify: should write multiple glyphs into a contiguous span with the run's own start/count")
val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 1u32, 1u32, 42u64,
    UI_PRODUCER_GUI, 1u32
)
expect(outcome.scene.text_runs.run_glyph_starts[0]).to_equal(0u32)
expect(outcome.scene.text_runs.run_glyph_counts[0]).to_equal(3u32)
expect(outcome.scene.text_runs.glyph_ids[0]).to_equal(1u32)
expect(outcome.scene.text_runs.glyph_ids[2]).to_equal(3u32)
```

</details>

#### should write multiple path points into a contiguous span with the span's own start/count

- should write multiple path points into a contiguous span with the span's own start/count
- Verify: should write multiple path points into a contiguous span with the span's own start/count
   - Expected: outcome.scene.path_points.span_point_starts[0] equals `0u32`
   - Expected: outcome.scene.path_points.span_point_counts[0] equals `4u32`
   - Expected: outcome.scene.path_points.point_xs[2] equals `10`
   - Expected: outcome.scene.path_points.point_ys[2] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should write multiple path points into a contiguous span with the span's own start/count")
step("Verify: should write multiple path points into a contiguous span with the span's own start/count")
val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 1u32, 1u32, 42u64,
    UI_PRODUCER_GUI, 1u32
)
expect(outcome.scene.path_points.span_point_starts[0]).to_equal(0u32)
expect(outcome.scene.path_points.span_point_counts[0]).to_equal(4u32)
expect(outcome.scene.path_points.point_xs[2]).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(outcome.scene.path_points.point_ys[2]).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### should give every item exactly one owner record with the right producer_kind and semantic id

- should give every item exactly one owner record with the right producer_kind and semantic id
- Verify: should give every item exactly one owner record with the right producer_kind and semantic id
   - Expected: outcome.owners.len() equals `4`
   - Expected: outcome.owners[i].producer_kind equals `UI_PRODUCER_GUI`
   - Expected: outcome.owners[i].semantic_id equals `100u32 + (i as u32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should give every item exactly one owner record with the right producer_kind and semantic id")
step("Verify: should give every item exactly one owner record with the right producer_kind and semantic id")
val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 1u32, 1u32, 42u64,
    UI_PRODUCER_GUI, 1u32
)
expect(outcome.owners.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
var i = 0
while i < outcome.owners.len():
    expect(outcome.owners[i].producer_kind).to_equal(UI_PRODUCER_GUI)
    expect(outcome.owners[i].semantic_id).to_equal(100u32 + (i as u32))
    i = i + 1
```

</details>

#### should link the image item's owner record to the correct ACTION_BINDINGS row

- should link the image item's owner record to the correct ACTION_BINDINGS row
- Verify: should link the image item's owner record to the correct ACTION_BINDINGS row
   - Expected: image_owner.action_binding_id equals `0u32`
   - Expected: outcome.actions[0].action_id equals `42u32`
   - Expected: outcome.actions[0].app_id equals `7u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should link the image item's owner record to the correct ACTION_BINDINGS row")
step("Verify: should link the image item's owner record to the correct ACTION_BINDINGS row")
val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 1u32, 1u32, 42u64,
    UI_PRODUCER_GUI, 1u32
)
val image_owner = outcome.owners[3]
expect(image_owner.action_binding_id).to_equal(0u32)
expect(outcome.actions[0].action_id).to_equal(42u32)
expect(outcome.actions[0].app_id).to_equal(7u32)
```

</details>

#### should point the provenance edge's command_index at the correct COMMANDS row

- should point the provenance edge's command_index at the correct COMMANDS row
- Verify: should point the provenance edge's command_index at the correct COMMANDS row
   - Expected: outcome.scene.provenance.command_indices[0] equals `0u32`
   - Expected: outcome.scene.provenance.source_node_ids[0] equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should point the provenance edge's command_index at the correct COMMANDS row")
step("Verify: should point the provenance edge's command_index at the correct COMMANDS row")
val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 1u32, 1u32, 42u64,
    UI_PRODUCER_GUI, 1u32
)
expect(outcome.scene.provenance.command_indices[0]).to_equal(0u32)
expect(outcome.scene.provenance.source_node_ids[0]).to_equal(1u32)
```

</details>

#### should derive one Prepared2DBatch and one DirtyRange covering the whole non-empty scene

- should derive one Prepared2DBatch and one DirtyRange covering the whole non-empty scene
- Verify: should derive one Prepared2DBatch and one DirtyRange covering the whole non-empty scene
   - Expected: outcome.prepared_batches[0].first_command equals `0u32`
   - Expected: outcome.prepared_batches[0].command_count equals `4u32`
   - Expected: outcome.dirty_ranges[0].start equals `0u32`
   - Expected: outcome.dirty_ranges[0].count equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should derive one Prepared2DBatch and one DirtyRange covering the whole non-empty scene")
step("Verify: should derive one Prepared2DBatch and one DirtyRange covering the whole non-empty scene")
val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 1u32, 1u32, 42u64,
    UI_PRODUCER_GUI, 1u32
)
expect(outcome.prepared_batches[0].first_command).to_equal(0u32)
expect(outcome.prepared_batches[0].command_count).to_equal(4u32)
expect(outcome.dirty_ranges[0].start).to_equal(0u32)
expect(outcome.dirty_ranges[0].count).to_equal(4u32)
```

</details>

#### should derive zero prepared batches and zero dirty ranges for an empty request

- should derive zero prepared batches and zero dirty ranges for an empty request
- Verify: should derive zero prepared batches and zero dirty ranges for an empty request
   - Expected: outcome.emitted is true
   - Expected: outcome.prepared_batches.len() equals `0`
   - Expected: outcome.dirty_ranges.len() equals `0`
   - Expected: outcome.scene.commands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should derive zero prepared batches and zero dirty ranges for an empty request")
step("Verify: should derive zero prepared batches and zero dirty ranges for an empty request")
val outcome = draw_ir_v3_emit_full_scene(
    draw_ir_v3_full_request_blank(), _generous_capacity(), 1u32, 1u32, 1u64,
    UI_PRODUCER_GUI, 1u32
)
expect(outcome.emitted).to_equal(true)
expect(outcome.prepared_batches.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(outcome.dirty_ranges.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(outcome.scene.commands.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### Determinism (same input twice -> byte-identical output)

#### should produce identical scenes, owners, actions and derived tables across two runs of the same request

- should produce identical scenes, owners, actions and derived tables across two runs of the same request
- Verify: should produce identical scenes, owners, actions and derived tables across two runs of the same request
   - Expected: outcome_a.scene.commands.len() equals `outcome_b.scene.commands.len()`
   - Expected: ca.kind equals `cb.kind`
   - Expected: ca.component_id equals `cb.component_id`
   - Expected: ca.geometry_id equals `cb.geometry_id`
   - Expected: ca.paint_id equals `cb.paint_id`
   - Expected: ca.text_run_id equals `cb.text_run_id`
   - Expected: ca.image_resource_id equals `cb.image_resource_id`
   - Expected: ca.path_span_id equals `cb.path_span_id`
   - Expected: ca.clip_id equals `cb.clip_id`
   - Expected: ca.transform_id equals `cb.transform_id`
   - Expected: ca.hit_shape_id equals `cb.hit_shape_id`
   - Expected: outcome_a.scene.geometry.xs.len() equals `outcome_b.scene.geometry.xs.len()`
   - Expected: outcome_a.scene.geometry.xs[g] equals `outcome_b.scene.geometry.xs[g]`
   - Expected: outcome_a.scene.geometry.ys[g] equals `outcome_b.scene.geometry.ys[g]`
   - Expected: outcome_a.scene.hit_shapes.xs.len() equals `outcome_b.scene.hit_shapes.xs.len()`
   - Expected: outcome_a.owners.len() equals `outcome_b.owners.len()`
   - Expected: outcome_a.owners[o].semantic_id equals `outcome_b.owners[o].semantic_id`
   - Expected: outcome_a.owners[o].action_binding_id equals `outcome_b.owners[o].action_binding_id`
   - Expected: outcome_a.prepared_batches.len() equals `outcome_b.prepared_batches.len()`
   - Expected: outcome_a.dirty_ranges[0].count equals `outcome_b.dirty_ranges[0].count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should produce identical scenes, owners, actions and derived tables across two runs of the same request")
step("Verify: should produce identical scenes, owners, actions and derived tables across two runs of the same request")
val outcome_a = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 5u32, 9u32, 42u64,
    UI_PRODUCER_GUI, 3u32
)
val outcome_b = draw_ir_v3_emit_full_scene(
    _fixture_request(), _generous_capacity(), 5u32, 9u32, 42u64,
    UI_PRODUCER_GUI, 3u32
)
expect(outcome_a.scene.commands.len()).to_equal(outcome_b.scene.commands.len())
var i = 0
while i < outcome_a.scene.commands.len():
    val ca = outcome_a.scene.commands[i]
    val cb = outcome_b.scene.commands[i]
    expect(ca.kind).to_equal(cb.kind)
    expect(ca.component_id).to_equal(cb.component_id)
    expect(ca.geometry_id).to_equal(cb.geometry_id)
    expect(ca.paint_id).to_equal(cb.paint_id)
    expect(ca.text_run_id).to_equal(cb.text_run_id)
    expect(ca.image_resource_id).to_equal(cb.image_resource_id)
    expect(ca.path_span_id).to_equal(cb.path_span_id)
    expect(ca.clip_id).to_equal(cb.clip_id)
    expect(ca.transform_id).to_equal(cb.transform_id)
    expect(ca.hit_shape_id).to_equal(cb.hit_shape_id)
    i = i + 1

expect(outcome_a.scene.geometry.xs.len()).to_equal(outcome_b.scene.geometry.xs.len())
var g = 0
while g < outcome_a.scene.geometry.xs.len():
    expect(outcome_a.scene.geometry.xs[g]).to_equal(outcome_b.scene.geometry.xs[g])
    expect(outcome_a.scene.geometry.ys[g]).to_equal(outcome_b.scene.geometry.ys[g])
    g = g + 1

expect(outcome_a.scene.hit_shapes.xs.len()).to_equal(outcome_b.scene.hit_shapes.xs.len())
expect(outcome_a.owners.len()).to_equal(outcome_b.owners.len())
var o = 0
while o < outcome_a.owners.len():
    expect(outcome_a.owners[o].semantic_id).to_equal(outcome_b.owners[o].semantic_id)
    expect(outcome_a.owners[o].action_binding_id).to_equal(outcome_b.owners[o].action_binding_id)
    o = o + 1

expect(outcome_a.prepared_batches.len()).to_equal(outcome_b.prepared_batches.len())
expect(outcome_a.dirty_ranges[0].count).to_equal(outcome_b.dirty_ranges[0].count)
```

</details>

### Capacity overflow (design section 5 VERIFY: refuse, never clamp)

#### should refuse with a CAPACITY receipt naming HIT_SHAPES and write nothing anywhere when capacity is one row short

- should refuse with a CAPACITY receipt naming HIT_SHAPES and write nothing anywhere when capacity is one row short
- Fixture needs 1 HIT_SHAPES row; capacity allows 0
   - Expected: outcome.emitted is false
   - Expected: outcome.overflow == nil is false
   - Expected: r.table_id equals `UI_SCENE_TABLE_HIT_SHAPES`
   - Expected: r.kind equals `UI_SCENE_OVERFLOW_CAPACITY`
   - Expected: r.required equals `1u32`
   - Expected: r.capacity equals `0u32`
- Zero rows anywhere -- not even in tables that would have fit
   - Expected: outcome.scene.commands.len() equals `0`
   - Expected: outcome.scene.geometry.xs.len() equals `0`
   - Expected: outcome.scene.paint.fill_colors.len() equals `0`
   - Expected: outcome.owners.len() equals `0`
   - Expected: outcome.actions.len() equals `0`
   - Expected: outcome.prepared_batches.len() equals `0`
   - Expected: outcome.dirty_ranges.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should refuse with a CAPACITY receipt naming HIT_SHAPES and write nothing anywhere when capacity is one row short")
step("Fixture needs 1 HIT_SHAPES row; capacity allows 0")
var cap = _generous_capacity()
cap = ui_scene_capacity_set(cap, UI_SCENE_TABLE_HIT_SHAPES, 0u32)

val outcome = draw_ir_v3_emit_full_scene(
    _fixture_request(), cap, 1u32, 1u32, 42u64, UI_PRODUCER_GUI, 1u32
)
expect(outcome.emitted).to_equal(false)
expect(outcome.overflow == nil).to_equal(false)
if val r = outcome.overflow:
    expect(r.table_id).to_equal(UI_SCENE_TABLE_HIT_SHAPES)
    expect(r.kind).to_equal(UI_SCENE_OVERFLOW_CAPACITY)
    expect(r.required).to_equal(1u32)
    expect(r.capacity).to_equal(0u32)

step("Zero rows anywhere -- not even in tables that would have fit")
expect(outcome.scene.commands.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(outcome.scene.geometry.xs.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(outcome.scene.paint.fill_colors.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(outcome.owners.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(outcome.actions.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(outcome.prepared_batches.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(outcome.dirty_ranges.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### Writer fail-closed contract (design section 2.3: Deficit/Surplus, never a silent clamp)

#### should report Exact when the writer is filled with exactly the reserved count

- should report Exact when the writer is filled with exactly the reserved count
- Verify: should report Exact when the writer is filled with exactly the reserved count
   - Expected: draw_ir_v3_verdict_is_exact(verdict) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report Exact when the writer is filled with exactly the reserved count")
step("Verify: should report Exact when the writer is filled with exactly the reserved count")
var counts = draw_ir_v3_emit_full_count(draw_ir_v3_full_request_blank())
counts.hit_shapes = 5u32
val reserved_range = UiSceneRange(start: 0u32, count: 5u32)
var reserved = _empty_ranges_with_hit_shapes(reserved_range)
var writer = draw_ir_v3_full_writer_create(counts, reserved)
var i = 0
while i < 5:
    writer.put_hit_shape(_blank_hit_shape())
    i = i + 1
val verdict = writer.finish()
expect(draw_ir_v3_verdict_is_exact(verdict)).to_equal(true)
```

</details>

#### should report DEFICIT with the missing row count when a producer under-fills HIT_SHAPES

- should report DEFICIT with the missing row count when a producer under-fills HIT_SHAPES
- Reserved 5 HIT_SHAPES rows; producer stub writes only 4
   - Expected: draw_ir_v3_verdict_is_exact(verdict) is false
   - Expected: table_id equals `UI_SCENE_TABLE_HIT_SHAPES`
   - Expected: n equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report DEFICIT with the missing row count when a producer under-fills HIT_SHAPES")
step("Reserved 5 HIT_SHAPES rows; producer stub writes only 4")
var counts = draw_ir_v3_emit_full_count(draw_ir_v3_full_request_blank())
counts.hit_shapes = 5u32
val reserved_range = UiSceneRange(start: 0u32, count: 5u32)
var reserved = _empty_ranges_with_hit_shapes(reserved_range)
var writer = draw_ir_v3_full_writer_create(counts, reserved)
var i = 0
while i < 4:
    writer.put_hit_shape(_blank_hit_shape())
    i = i + 1
val verdict = writer.finish()
expect(draw_ir_v3_verdict_is_exact(verdict)).to_equal(false)
match verdict:
    case UiSceneWriteVerdict.Deficit(table_id, n):
        expect(table_id).to_equal(UI_SCENE_TABLE_HIT_SHAPES)
        expect(n).to_equal(1u32)
    case _:
        assert_true(false)
```

</details>

#### should report SURPLUS with the extra row count when a producer over-fills HIT_SHAPES

- should report SURPLUS with the extra row count when a producer over-fills HIT_SHAPES
- Physical capacity 6, reserved quota 5; producer stub writes 6
   - Expected: draw_ir_v3_verdict_is_exact(verdict) is false
   - Expected: table_id equals `UI_SCENE_TABLE_HIT_SHAPES`
   - Expected: n equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report SURPLUS with the extra row count when a producer over-fills HIT_SHAPES")
step("Physical capacity 6, reserved quota 5; producer stub writes 6")
var counts = draw_ir_v3_emit_full_count(draw_ir_v3_full_request_blank())
counts.hit_shapes = 6u32
val reserved_range = UiSceneRange(start: 0u32, count: 5u32)
var reserved = _empty_ranges_with_hit_shapes(reserved_range)
var writer = draw_ir_v3_full_writer_create(counts, reserved)
var i = 0
while i < 6:
    writer.put_hit_shape(_blank_hit_shape())
    i = i + 1
val verdict = writer.finish()
expect(draw_ir_v3_verdict_is_exact(verdict)).to_equal(false)
match verdict:
    case UiSceneWriteVerdict.Surplus(table_id, n):
        expect(table_id).to_equal(UI_SCENE_TABLE_HIT_SHAPES)
        expect(n).to_equal(1u32)
    case _:
        assert_true(false)
```

</details>

#### should refuse a put_hit_shape call once the physical array bound is reached

- should refuse a put_hit_shape call once the physical array bound is reached
- Physical capacity 5, reserved quota 5: a 6th write must be refused outright
   - Expected: ok is true
   - Expected: overflow_write is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should refuse a put_hit_shape call once the physical array bound is reached")
step("Physical capacity 5, reserved quota 5: a 6th write must be refused outright")
var counts = draw_ir_v3_emit_full_count(draw_ir_v3_full_request_blank())
counts.hit_shapes = 5u32
val reserved_range = UiSceneRange(start: 0u32, count: 5u32)
var reserved = _empty_ranges_with_hit_shapes(reserved_range)
var writer = draw_ir_v3_full_writer_create(counts, reserved)
var i = 0
while i < 5:
    val ok = writer.put_hit_shape(_blank_hit_shape())
    expect(ok).to_equal(true)
    i = i + 1
val overflow_write = writer.put_hit_shape(_blank_hit_shape())
expect(overflow_write).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `c8170ad5b5d08d3d1193b53bd0b1d93c3ef9972c79230967d86d6e7b82010198`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c8170ad5b5d08d3d1193b53bd0b1d93c3ef9972c79230967d86d6e7b82010198`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c8170ad5b5d08d3d1193b53bd0b1d93c3ef9972c79230967d86d6e7b82010198`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:175:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should auto-assign sequential ids only to items that did not set one' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should auto-assign sequential ids only to items that did not set one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:196:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should count exact per-table rows for the mixed fixture before any emission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:196:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should count exact per-table rows for the mixed fixture before any emission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:218:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit exactly the counted rows into every one of the 16 tables' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should emit exactly the counted rows into every one of the 16 tables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:245:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should leave geometry_id/paint_id/etc as NO_ID on a command whose item did not request that table' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:260:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should write multiple glyphs into a contiguous span with the run's own start/count' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl:273:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should write multiple path points into a contiguous span with the span's own start/count' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
