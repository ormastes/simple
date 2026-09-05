# ui_scene_ports_v2_spec

> Purpose: Prove that UiPackedProducer / writer contract (design section 2.2, 2.3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ui_scene_ports_v2_spec

Purpose: Prove that UiPackedProducer / writer contract (design section 2.2, 2.3).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that UiPackedProducer / writer contract (design section 2.2, 2.3).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### UiPackedProducer / writer contract (design section 2.2, 2.3)

#### should emit a slice when the producer writes exactly the reserved COMMANDS rows

- A writer reserved for 2 commands, a producer that writes exactly 2
   - Expected: slice.scene_slot equals `1u32`
   - Expected: slice.scene_generation equals `1u32`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-COMMON-001
step("A writer reserved for 2 commands, a producer that writes exactly 2")
val writer = FakeDrawIrV3Writer(command_count: 0u32, command_cap: 2u32)
val owners = FakeUiOwnerWriter(count: 0u32, cap: 0u32)
val actions = FakeUiActionWriter(count: 0u32)
val producer = FakeUiPackedProducer(kind: UI_PRODUCER_GUI, id_val: 5u32, commands_to_emit: 2u32)

val result = producer.emit(1u64, ui_scene_ranges_zero(), writer, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        expect(slice.scene_slot).to_equal(1u32)
        expect(slice.scene_generation).to_equal(1u32)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
```

</details>

#### should refuse with a Deficit receipt when the producer writes fewer rows than reserved

- should refuse with a Deficit receipt when the producer writes fewer rows than reserved
- A writer reserved for 3 commands, a producer that writes only 2
   - Expected: true is false
   - Expected: receipt.table_id equals `UI_SCENE_TABLE_COMMANDS`
   - Expected: receipt.required equals `1u32`
   - Expected: receipt.kind equals `UI_SCENE_OVERFLOW_DEFICIT`
   - Expected: receipt.snapshot_id equals `9u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should refuse with a Deficit receipt when the producer writes fewer rows than reserved")
step("A writer reserved for 3 commands, a producer that writes only 2")
val writer = FakeDrawIrV3Writer(command_count: 0u32, command_cap: 3u32)
val owners = FakeUiOwnerWriter(count: 0u32, cap: 0u32)
val actions = FakeUiActionWriter(count: 0u32)
val producer = FakeUiPackedProducer(kind: UI_PRODUCER_GUI, id_val: 5u32, commands_to_emit: 2u32)

val result = producer.emit(9u64, ui_scene_ranges_zero(), writer, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        expect(true).to_equal(false)
    UiSceneEmitResult.Refused(receipt):
        expect(receipt.table_id).to_equal(UI_SCENE_TABLE_COMMANDS)
        expect(receipt.required).to_equal(1u32)
        expect(receipt.kind).to_equal(UI_SCENE_OVERFLOW_DEFICIT)
        expect(receipt.snapshot_id).to_equal(9u64)
```

</details>

#### should refuse a bounds-checked put_command once the writer's capacity is reached

- should refuse a bounds-checked put_command once the writer's capacity is reached
- A writer reserved for 1 command sees 2 attempted writes
   - Expected: first is true
   - Expected: second is false
   - Expected: writer.cursor(UI_SCENE_TABLE_COMMANDS) equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should refuse a bounds-checked put_command once the writer's capacity is reached")
step("A writer reserved for 1 command sees 2 attempted writes")
val writer = FakeDrawIrV3Writer(command_count: 0u32, command_cap: 1u32)
val first = writer.put_command(draw_ir_v3_empty_command())
val second = writer.put_command(draw_ir_v3_empty_command())

expect(first).to_equal(true)
expect(second).to_equal(false)
expect(writer.cursor(UI_SCENE_TABLE_COMMANDS)).to_equal(1u32)
```

</details>

#### should construct a UiSceneWriteVerdict.Surplus carrying the table and overage

- should construct a UiSceneWriteVerdict.Surplus carrying the table and overage
- Verify: should construct a UiSceneWriteVerdict.Surplus carrying the table and overage
   - Expected: true is false
   - Expected: true is false
   - Expected: table_id equals `UI_SCENE_TABLE_COMMANDS`
   - Expected: n equals `5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct a UiSceneWriteVerdict.Surplus carrying the table and overage")
step("Verify: should construct a UiSceneWriteVerdict.Surplus carrying the table and overage")
val verdict = UiSceneWriteVerdict.Surplus(table_id: UI_SCENE_TABLE_COMMANDS, n: 5u32)
match verdict:
    UiSceneWriteVerdict.Exact:
        expect(true).to_equal(false)
    UiSceneWriteVerdict.Deficit(table_id, n):
        expect(true).to_equal(false)
    UiSceneWriteVerdict.Surplus(table_id, n):
        expect(table_id).to_equal(UI_SCENE_TABLE_COMMANDS)
        expect(n).to_equal(5u32)
```

</details>

#### should let an owner writer reach Exact when the reserved row count is written

- should let an owner writer reach Exact when the reserved row count is written
- Verify: should let an owner writer reach Exact when the reserved row count is written
   - Expected: put_ok is true
   - Expected: owners.cursor() equals `1u32`
   - Expected: true is false
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should let an owner writer reach Exact when the reserved row count is written")
step("Verify: should let an owner writer reach Exact when the reserved row count is written")
val owners = FakeUiOwnerWriter(count: 0u32, cap: 1u32)
val put_ok = owners.put_owner_record(
    UiOwnerRecord(
        producer_kind: UI_PRODUCER_GUI, event_policy: 0u16,
        semantic_id: 1u32, semantic_generation: 1u32,
        parent_owner_id: DRAW_IR_V3_NO_ID, action_binding_id: DRAW_IR_V3_NO_ID
    )
)
expect(put_ok).to_equal(true)
match owners.finish():
    UiSceneWriteVerdict.Exact:
        expect(owners.cursor()).to_equal(1u32)
    UiSceneWriteVerdict.Deficit(table_id, n):
        expect(true).to_equal(false)
    UiSceneWriteVerdict.Surplus(table_id, n):
        expect(true).to_equal(false)
```

</details>

#### should construct a UiSceneSlice directly from its four fields

- should construct a UiSceneSlice directly from its four fields
- Verify: should construct a UiSceneSlice directly from its four fields
   - Expected: slice.scene_slot equals `3u32`
   - Expected: slice.scene_generation equals `7u32`
   - Expected: slice.root_component_id equals `11u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct a UiSceneSlice directly from its four fields")
step("Verify: should construct a UiSceneSlice directly from its four fields")
val slice = UiSceneSlice(
    scene_slot: 3u32, scene_generation: 7u32,
    root_component_id: 11u32, ranges: ui_scene_ranges_zero()
)
expect(slice.scene_slot).to_equal(3u32)
expect(slice.scene_generation).to_equal(7u32)
expect(slice.root_component_id).to_equal(11u32)
```

</details>

#### should track an action writer's row count via cursor

- should track an action writer's row count via cursor
- Verify: should track an action writer's row count via cursor
   - Expected: actions.cursor() equals `2u32`
   - Expected: true is true
   - Expected: true is false
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should track an action writer's row count via cursor")
step("Verify: should track an action writer's row count via cursor")
val actions = FakeUiActionWriter(count: 0u32)
val binding = MenuActionBinding(
    app_id: 1u32, app_generation: 1u32, menu_revision: 1u32,
    action_id: 2u32, default_target_owner_id: DRAW_IR_V3_NO_ID
)
actions.put_action_binding(binding)
actions.put_action_binding(binding)
expect(actions.cursor()).to_equal(2u32)
match actions.finish():
    UiSceneWriteVerdict.Exact:
        expect(true).to_equal(true)
    UiSceneWriteVerdict.Deficit(table_id, n):
        expect(true).to_equal(false)
    UiSceneWriteVerdict.Surplus(table_id, n):
        expect(true).to_equal(false)
```

</details>

### PackedDrawPortV2 / versioned reference submission (design section 2.6)

#### should accept a submission when scene and Prepared2D generations match

- should accept a submission when scene and Prepared2D generations match
- Verify: should accept a submission when scene and Prepared2D generations match
   - Expected: receipt.accepted is true
   - Expected: receipt.reason equals `DRAW_IR_V3_PORT_V2_REASON_OK`
   - Expected: receipt.scene_generation equals `4u32`
   - Expected: receipt.commands_seen equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should accept a submission when scene and Prepared2D generations match")
step("Verify: should accept a submission when scene and Prepared2D generations match")
val port = FakePackedDrawPortV2(caps: 3u32, present_ok: true)
val scene = PackedSceneRef(object_slot: 1u32, object_generation: 1u32, scene_id: 9u32, scene_generation: 4u32)
val prepared = Prepared2DRef(batches: UiSceneRange(start: 0u32, count: 2u32), scene_generation: 4u32)
val dirty = DirtyRangeRef(dirty_upload: UiSceneRange(start: 0u32, count: 1u32), scene_generation: 4u32)

val receipt = port.submit_scene_ref(scene, prepared, dirty)
expect(receipt.accepted).to_equal(true)
expect(receipt.reason).to_equal(DRAW_IR_V3_PORT_V2_REASON_OK)
expect(receipt.scene_generation).to_equal(4u32)
expect(receipt.commands_seen).to_equal(4u32)
```

</details>

#### should refuse a submission when the Prepared2D generation is stale relative to the scene

- should refuse a submission when the Prepared2D generation is stale relative to the scene
- Verify: should refuse a submission when the Prepared2D generation is stale relative to the scene
   - Expected: receipt.accepted is false
   - Expected: receipt.reason equals `DRAW_IR_V3_PORT_V2_REASON_STALE_GENERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should refuse a submission when the Prepared2D generation is stale relative to the scene")
step("Verify: should refuse a submission when the Prepared2D generation is stale relative to the scene")
val port = FakePackedDrawPortV2(caps: 3u32, present_ok: true)
val scene = PackedSceneRef(object_slot: 1u32, object_generation: 1u32, scene_id: 9u32, scene_generation: 5u32)
val prepared = Prepared2DRef(batches: UiSceneRange(start: 0u32, count: 2u32), scene_generation: 4u32)
val dirty = DirtyRangeRef(dirty_upload: UiSceneRange(start: 0u32, count: 1u32), scene_generation: 5u32)

val receipt = port.submit_scene_ref(scene, prepared, dirty)
expect(receipt.accepted).to_equal(false)
expect(receipt.reason).to_equal(DRAW_IR_V3_PORT_V2_REASON_STALE_GENERATION)
```

</details>

#### should report present() as a pass-through capability call

- should report present() as a pass-through capability call
- Verify: should report present() as a pass-through capability call
   - Expected: ok_port.present(4u32) is true
   - Expected: down_port.present(4u32) is false
   - Expected: ok_port.capabilities() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report present() as a pass-through capability call")
step("Verify: should report present() as a pass-through capability call")
val ok_port = FakePackedDrawPortV2(caps: 1u32, present_ok: true)
val down_port = FakePackedDrawPortV2(caps: 1u32, present_ok: false)
expect(ok_port.present(4u32)).to_equal(true)
expect(down_port.present(4u32)).to_equal(false)
expect(ok_port.capabilities()).to_equal(1u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `00514fca6bd72f58c4af8385c9942e06a180b1f557f794240a5dc8375e083342`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00514fca6bd72f58c4af8385c9942e06a180b1f557f794240a5dc8375e083342`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00514fca6bd72f58c4af8385c9942e06a180b1f557f794240a5dc8375e083342`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/ui_scene_ports_v2_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/ui_scene_ports_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/ui_scene_ports_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:217:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit a slice when the producer writes exactly the reserved COMMANDS rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:217:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should emit a slice when the producer writes exactly the reserved COMMANDS rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:233:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse with a Deficit receipt when the producer writes fewer rows than reserved' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:233:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should refuse with a Deficit receipt when the producer writes fewer rows than reserved' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:252:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse a bounds-checked put_command once the writer's capacity is reached' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:252:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should refuse a bounds-checked put_command once the writer's capacity is reached' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:264:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct a UiSceneWriteVerdict.Surplus carrying the table and overage' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:278:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should let an owner writer reach Exact when the reserved row count is written' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl:299:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct a UiSceneSlice directly from its four fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
