# Ui Scene Arena Specification

> Tests covering UiSceneArena allocate-once buffer reuse (design section 3), UiSceneNativeWriter bounds-checked cursor writes (design section 2.3), UiSceneNativeOwnerWriter / UiSceneNativeActionWriter reserved sub-ranges (design section 2.3), UiSceneArena completion-gated swap (design section 3), UiSceneArena front read view (design section 3), UiScenePackedPortV2 stable reference submission (design section 2.6), UiSceneV1CompatPort v1-to-arena round trip (design section 2.6).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Scene Arena Specification

## Scenarios

### UiSceneArena allocate-once buffer reuse (design section 3)

#### reports alloc_count == 1 immediately after construction

- reports alloc_count == 1 immediately after construction
   - Expected: arena.alloc_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports alloc_count == 1 immediately after construction")
val arena = UiSceneArena.new(_test_capacity())
expect(arena.alloc_count()).to_equal(1u32)
```

</details>

#### leaves alloc_count unchanged after two back-to-back write+swap generations

- leaves alloc_count unchanged after two back-to-back write+swap generations
- Arena constructed; record the allocation counter baseline
- Generation 1: write 2 commands, commit, signal, swap
   - Expected: _write_and_swap_commands(arena, [1u16, 1u16], [1u32, 2u32]) is true
- Generation 2: write into what is now the back generation -- the SAME physical columns that were front before generation 1
   - Expected: _write_and_swap_commands(arena, [2u16, 2u16, 2u16], [3u32, 4u32, 5u32]) is true
   - Expected: arena.alloc_count() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves alloc_count unchanged after two back-to-back write+swap generations")
step("Arena constructed; record the allocation counter baseline")
val arena = UiSceneArena.new(_test_capacity())
val before = arena.alloc_count()

step("Generation 1: write 2 commands, commit, signal, swap")
expect(_write_and_swap_commands(arena, [1u16, 1u16], [1u32, 2u32])).to_equal(true)

step("Generation 2: write into what is now the back generation -- the SAME physical columns that were front before generation 1")
expect(_write_and_swap_commands(arena, [2u16, 2u16, 2u16], [3u32, 4u32, 5u32])).to_equal(true)

expect(arena.alloc_count()).to_equal(before)
```

</details>

### UiSceneNativeWriter bounds-checked cursor writes (design section 2.3)

#### writes exactly the reserved COMMANDS rows and finishes Exact

- writes exactly the reserved COMMANDS rows and finishes Exact
   - Expected: writer.put_command(_test_command(9u16, 1u32)) is true
   - Expected: writer.put_command(_test_command(9u16, 2u32)) is true
   - Expected: true is true
   - Expected: true is false
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("writes exactly the reserved COMMANDS rows and finishes Exact")
val ranges = _commands_range(2u32)
val writer = UiSceneNativeWriter.new(ranges)
expect(writer.put_command(_test_command(9u16, 1u32))).to_equal(true)
expect(writer.put_command(_test_command(9u16, 2u32))).to_equal(true)
match writer.finish():
    UiSceneWriteVerdict.Exact:
        expect(true).to_equal(true)
    UiSceneWriteVerdict.Deficit(table_id, n):
        expect(true).to_equal(false)
    UiSceneWriteVerdict.Surplus(table_id, n):
        expect(true).to_equal(false)
```

</details>

#### refuses a write past the reserved range and invalidates the generation

- refuses a write past the reserved range and invalidates the generation
   - Expected: writer.put_command(_test_command(9u16, 1u32)) is true
   - Expected: writer.put_command(_test_command(9u16, 2u32)) is false
   - Expected: writer.is_valid() is false
- Committing an invalidated writer refuses and marks the back generation invalid
   - Expected: ui_scene_commit_draw_write(arena, writer, ranges) is false
   - Expected: arena.back_is_valid() is false
- An invalidated generation must never become the visible front
   - Expected: arena.try_swap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a write past the reserved range and invalidates the generation")
val arena = UiSceneArena.new(_test_capacity())
arena.begin_generation()
val ranges = _commands_range(1u32)
val writer = UiSceneNativeWriter.new(ranges)
expect(writer.put_command(_test_command(9u16, 1u32))).to_equal(true)
expect(writer.put_command(_test_command(9u16, 2u32))).to_equal(false)
expect(writer.is_valid()).to_equal(false)

step("Committing an invalidated writer refuses and marks the back generation invalid")
expect(ui_scene_commit_draw_write(arena, writer, ranges)).to_equal(false)
expect(arena.back_is_valid()).to_equal(false)

step("An invalidated generation must never become the visible front")
arena.signal_front_complete()
expect(arena.try_swap()).to_equal(false)
```

</details>

#### reports Deficit naming the exact shortfall when fewer rows are written than reserved

- reports Deficit naming the exact shortfall when fewer rows are written than reserved
   - Expected: true is false
   - Expected: table_id equals `UI_SCENE_TABLE_COMMANDS`
   - Expected: n equals `1u32`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports Deficit naming the exact shortfall when fewer rows are written than reserved")
val ranges = _commands_range(3u32)
val writer = UiSceneNativeWriter.new(ranges)
writer.put_command(_test_command(1u16, 1u32))
writer.put_command(_test_command(1u16, 2u32))
match writer.finish():
    UiSceneWriteVerdict.Exact:
        expect(true).to_equal(false)
    UiSceneWriteVerdict.Deficit(table_id, n):
        expect(table_id).to_equal(UI_SCENE_TABLE_COMMANDS)
        expect(n).to_equal(1u32)
    UiSceneWriteVerdict.Surplus(table_id, n):
        expect(true).to_equal(false)
```

</details>

### UiSceneNativeOwnerWriter / UiSceneNativeActionWriter reserved sub-ranges (design section 2.3)

#### writes owner records within their reserved range and reports Exact

- writes owner records within their reserved range and reports Exact
   - Expected: writer.put_owner_record(_test_owner_row()) is true
   - Expected: writer.put_owner_record(_test_owner_row()) is true
   - Expected: writer.cursor() equals `2u32`
   - Expected: true is true
   - Expected: true is false
   - Expected: true is false
   - Expected: ui_scene_commit_owner_write(arena, writer, range) is true
   - Expected: arena.back_is_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("writes owner records within their reserved range and reports Exact")
val arena = UiSceneArena.new(_test_capacity())
val range = UiSceneRange(start: 0u32, count: 2u32)
val writer = UiSceneNativeOwnerWriter.new(range)
expect(writer.put_owner_record(_test_owner_row())).to_equal(true)
expect(writer.put_owner_record(_test_owner_row())).to_equal(true)
expect(writer.cursor()).to_equal(2u32)
match writer.finish():
    UiSceneWriteVerdict.Exact:
        expect(true).to_equal(true)
    UiSceneWriteVerdict.Deficit(table_id, n):
        expect(true).to_equal(false)
    UiSceneWriteVerdict.Surplus(table_id, n):
        expect(true).to_equal(false)
expect(ui_scene_commit_owner_write(arena, writer, range)).to_equal(true)
expect(arena.back_is_valid()).to_equal(true)
```

</details>

#### refuses a write past the owner range's reserved count and invalidates the generation

- refuses a write past the owner range's reserved count and invalidates the generation
   - Expected: writer.put_owner_record(_test_owner_row()) is false
   - Expected: writer.is_valid() is false
   - Expected: ui_scene_commit_owner_write(arena, writer, range) is false
   - Expected: arena.back_is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a write past the owner range's reserved count and invalidates the generation")
val arena = UiSceneArena.new(_test_capacity())
val range = UiSceneRange(start: 0u32, count: 2u32)
val writer = UiSceneNativeOwnerWriter.new(range)
writer.put_owner_record(_test_owner_row())
writer.put_owner_record(_test_owner_row())
expect(writer.put_owner_record(_test_owner_row())).to_equal(false)
expect(writer.is_valid()).to_equal(false)
expect(ui_scene_commit_owner_write(arena, writer, range)).to_equal(false)
expect(arena.back_is_valid()).to_equal(false)
```

</details>

#### writes action bindings within their reserved range and tracks cursor

- writes action bindings within their reserved range and tracks cursor
   - Expected: writer.put_action_binding(binding) is true
   - Expected: writer.put_action_binding(binding) is false
   - Expected: writer.cursor() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("writes action bindings within their reserved range and tracks cursor")
val range = UiSceneRange(start: 0u32, count: 1u32)
val writer = UiSceneNativeActionWriter.new(range)
val binding = MenuActionBinding(
    app_id: 1u32, app_generation: 1u32, menu_revision: 1u32,
    action_id: 2u32, default_target_owner_id: DRAW_IR_V3_NO_ID
)
expect(writer.put_action_binding(binding)).to_equal(true)
expect(writer.put_action_binding(binding)).to_equal(false)
expect(writer.cursor()).to_equal(1u32)
```

</details>

### UiSceneArena completion-gated swap (design section 3)

#### refuses swap before the completion signal, and the same swap after signal succeeds

- refuses swap before the completion signal, and the same swap after signal succeeds
   - Expected: ui_scene_commit_draw_write(arena, writer, ranges) is true
   - Expected: arena.try_swap() is false
   - Expected: arena.front_generation_id() equals `generation_before`
   - Expected: arena.try_swap() is true
   - Expected: arena.front_generation_id() equals `generation_before + 1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses swap before the completion signal, and the same swap after signal succeeds")
val arena = UiSceneArena.new(_test_capacity())
arena.begin_generation()
val ranges = _commands_range(1u32)
val writer = UiSceneNativeWriter.new(ranges)
writer.put_command(_test_command(1u16, 1u32))
writer.finish()
expect(ui_scene_commit_draw_write(arena, writer, ranges)).to_equal(true)

val generation_before = arena.front_generation_id()
expect(arena.try_swap()).to_equal(false)
expect(arena.front_generation_id()).to_equal(generation_before)

arena.signal_front_complete()
expect(arena.try_swap()).to_equal(true)
expect(arena.front_generation_id()).to_equal(generation_before + 1u32)
```

</details>

#### requires a fresh completion signal before each subsequent swap

- requires a fresh completion signal before each subsequent swap
   - Expected: _write_and_swap_commands(arena, [1u16], [1u32]) is true
   - Expected: ui_scene_commit_draw_write(arena, writer2, ranges2) is true
- No signal_front_complete() call this time
   - Expected: arena.try_swap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires a fresh completion signal before each subsequent swap")
val arena = UiSceneArena.new(_test_capacity())
expect(_write_and_swap_commands(arena, [1u16], [1u32])).to_equal(true)

arena.begin_generation()
val ranges2 = _commands_range(1u32)
val writer2 = UiSceneNativeWriter.new(ranges2)
writer2.put_command(_test_command(1u16, 2u32))
writer2.finish()
expect(ui_scene_commit_draw_write(arena, writer2, ranges2)).to_equal(true)
step("No signal_front_complete() call this time")
expect(arena.try_swap()).to_equal(false)
```

</details>

### UiSceneArena front read view (design section 3)

#### exposes only the front generation's committed rows, unaffected by an in-progress back write

- exposes only the front generation's committed rows, unaffected by an in-progress back write
   - Expected: _write_and_swap_commands(arena, [9u16], [42u32]) is true
   - Expected: arena.front_generation_id() equals `1u32`
   - Expected: arena.front_command_at(0u32).kind equals `9u16`
   - Expected: arena.front_command_at(0u32).component_id equals `42u32`
- Start generation 2's write but never swap -- the front view must still read generation 1
   - Expected: arena.front_generation_id() equals `1u32`
   - Expected: arena.front_command_at(0u32).kind equals `9u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes only the front generation's committed rows, unaffected by an in-progress back write")
val arena = UiSceneArena.new(_test_capacity())
expect(_write_and_swap_commands(arena, [9u16], [42u32])).to_equal(true)

expect(arena.front_generation_id()).to_equal(1u32)
expect(arena.front_command_at(0u32).kind).to_equal(9u16)
expect(arena.front_command_at(0u32).component_id).to_equal(42u32)

step("Start generation 2's write but never swap -- the front view must still read generation 1")
arena.begin_generation()
val ranges2 = _commands_range(1u32)
val writer2 = UiSceneNativeWriter.new(ranges2)
writer2.put_command(_test_command(77u16, 99u32))
writer2.finish()
ui_scene_commit_draw_write(arena, writer2, ranges2)

expect(arena.front_generation_id()).to_equal(1u32)
expect(arena.front_command_at(0u32).kind).to_equal(9u16)
```

</details>

### UiScenePackedPortV2 stable reference submission (design section 2.6)

#### refuses a PackedSceneRef carrying a stale object_generation

- refuses a PackedSceneRef carrying a stale object_generation
   - Expected: receipt.accepted is false
   - Expected: receipt.reason equals `DRAW_IR_V3_PORT_V2_REASON_STALE_GENERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a PackedSceneRef carrying a stale object_generation")
val arena = UiSceneArena.new(_test_capacity())
val port = UiScenePackedPortV2.new(arena, 5u32)
val stale_ref = PackedSceneRef(object_slot: 1u32, object_generation: 4u32, scene_id: 1u32, scene_generation: 1u32)
val prepared = Prepared2DRef(batches: UiSceneRange(start: 0u32, count: 0u32), scene_generation: 1u32)
val dirty = DirtyRangeRef(dirty_upload: UiSceneRange(start: 0u32, count: 0u32), scene_generation: 1u32)

val receipt = port.submit_scene_ref(stale_ref, prepared, dirty)
expect(receipt.accepted).to_equal(false)
expect(receipt.reason).to_equal(DRAW_IR_V3_PORT_V2_REASON_STALE_GENERATION)
```

</details>

#### accepts a PackedSceneRef with a fresh object_generation

- accepts a PackedSceneRef with a fresh object_generation
   - Expected: receipt.accepted is true
   - Expected: receipt.reason equals `DRAW_IR_V3_PORT_V2_REASON_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a PackedSceneRef with a fresh object_generation")
val arena = UiSceneArena.new(_test_capacity())
val port = UiScenePackedPortV2.new(arena, 5u32)
val fresh_ref = PackedSceneRef(object_slot: 1u32, object_generation: 5u32, scene_id: 1u32, scene_generation: 1u32)
val prepared = Prepared2DRef(batches: UiSceneRange(start: 0u32, count: 0u32), scene_generation: 1u32)
val dirty = DirtyRangeRef(dirty_upload: UiSceneRange(start: 0u32, count: 0u32), scene_generation: 1u32)

val receipt = port.submit_scene_ref(fresh_ref, prepared, dirty)
expect(receipt.accepted).to_equal(true)
expect(receipt.reason).to_equal(DRAW_IR_V3_PORT_V2_REASON_OK)
```

</details>

#### reports present() against the arena's current front generation

- reports present() against the arena's current front generation
   - Expected: port.present(0u32) is true
   - Expected: port.present(1u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports present() against the arena's current front generation")
val arena = UiSceneArena.new(_test_capacity())
val port = UiScenePackedPortV2.new(arena, 1u32)
expect(port.present(0u32)).to_equal(true)
expect(port.present(1u32)).to_equal(false)
```

</details>

### UiSceneV1CompatPort v1-to-arena round trip (design section 2.6)

#### round-trips submitted commands field-for-field through the arena

- round-trips submitted commands field-for-field through the arena
   - Expected: receipt.accepted is true
   - Expected: receipt.scene_generation equals `7u64`
   - Expected: v1_port.committed_command_count() equals `2u32`
   - Expected: actual.kind equals `expected.kind`
   - Expected: actual.flags equals `expected.flags`
   - Expected: actual.component_id equals `expected.component_id`
   - Expected: actual.component_generation equals `expected.component_generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips submitted commands field-for-field through the arena")
val arena = UiSceneArena.new(_test_capacity())
val v1_port = UiSceneV1CompatPort.new(arena)

var commands: [DrawIrV3Command] = []
commands.push(_test_command(3u16, 100u32))
commands.push(_test_command(4u16, 101u32))
val scene = DrawIrV3Scene(
    schema: "test-v1-compat", schema_id: 3u32, scene_id: 1u32, generation: 7u32,
    commands: commands,
    geometry: draw_ir_v3_empty_geometry_table(),
    paint: draw_ir_v3_empty_paint_table(),
    text_runs: draw_ir_v3_empty_text_run_table(),
    resources: draw_ir_v3_empty_resource_table(),
    path_points: draw_ir_v3_empty_path_point_table(),
    clips: draw_ir_v3_empty_clip_table(),
    transforms: draw_ir_v3_empty_transform_table(),
    hit_shapes: draw_ir_v3_empty_hit_shape_table(),
    provenance: draw_ir_v3_empty_provenance_table()
)

val receipt = v1_port.submit_scene(scene)
expect(receipt.accepted).to_equal(true)
expect(receipt.scene_generation).to_equal(7u64)

expect(v1_port.committed_command_count()).to_equal(2u32)
var i = 0
while i < commands.len():
    val expected = commands[i]
    val actual = v1_port.committed_command_at(i.to_u32())
    expect(actual.kind).to_equal(expected.kind)
    expect(actual.flags).to_equal(expected.flags)
    expect(actual.component_id).to_equal(expected.component_id)
    expect(actual.component_generation).to_equal(expected.component_generation)
    i = i + 1
```

</details>

#### refuses when the submitted scene exceeds COMMANDS capacity

- refuses when the submitted scene exceeds COMMANDS capacity
   - Expected: receipt.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses when the submitted scene exceeds COMMANDS capacity")
val arena = UiSceneArena.new(_test_capacity())
val v1_port = UiSceneV1CompatPort.new(arena)

var commands: [DrawIrV3Command] = []
var i = 0
while i < 9:
    commands.push(_test_command(1u16, i.to_u32()))
    i = i + 1
val scene = DrawIrV3Scene(
    schema: "test-v1-compat", schema_id: 3u32, scene_id: 1u32, generation: 1u32,
    commands: commands,
    geometry: draw_ir_v3_empty_geometry_table(),
    paint: draw_ir_v3_empty_paint_table(),
    text_runs: draw_ir_v3_empty_text_run_table(),
    resources: draw_ir_v3_empty_resource_table(),
    path_points: draw_ir_v3_empty_path_point_table(),
    clips: draw_ir_v3_empty_clip_table(),
    transforms: draw_ir_v3_empty_transform_table(),
    hit_shapes: draw_ir_v3_empty_hit_shape_table(),
    provenance: draw_ir_v3_empty_provenance_table()
)

val receipt = v1_port.submit_scene(scene)
expect(receipt.accepted).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UiSceneArena allocate-once buffer reuse (design section 3), UiSceneNativeWriter bounds-checked cursor writes (design section 2.3), UiSceneNativeOwnerWriter / UiSceneNativeActionWriter reserved sub-ranges (design section 2.3), UiSceneArena completion-gated swap (design section 3), UiSceneArena front read view (design section 3), UiScenePackedPortV2 stable reference submission (design section 2.6), UiSceneV1CompatPort v1-to-arena round trip (design section 2.6).
- UiSceneArena allocate-once buffer reuse (design section 3)
- UiSceneNativeWriter bounds-checked cursor writes (design section 2.3)
- UiSceneNativeOwnerWriter / UiSceneNativeActionWriter reserved sub-ranges (design section 2.3)
- UiSceneArena completion-gated swap (design section 3)
- UiSceneArena front read view (design section 3)
- UiScenePackedPortV2 stable reference submission (design section 2.6)
- UiSceneV1CompatPort v1-to-arena round trip (design section 2.6)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e39c9288035a59672971519f2dd2ad205035f497497ffa3e74d8df607b225d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e39c9288035a59672971519f2dd2ad205035f497497ffa3e74d8df607b225d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e39c9288035a59672971519f2dd2ad205035f497497ffa3e74d8df607b225d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports alloc_count == 1 immediately after construction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves alloc_count unchanged after two back-to-back write+swap generations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes exactly the reserved COMMANDS rows and finishes Exact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
