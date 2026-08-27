# Ui Web Packed Producer Specification

> Tests covering WebPackedProducer count/emit exactness (design section 2.2, lane L7), WebPackedProducer owner records (design section 2.4, gate b), WebPackedProducer host_owner_id reparenting (cross-producer owner-chain wiring), WebPackedProducer WebView nesting (design section 2.2 nesting rule, gate c/d), WebPackedProducer id rebasing under a non-zero assigned range (multi-producer composition), WebPackedProducer parity with the v2 oracle (design section 9, gate d).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Web Packed Producer Specification

## Scenarios

### WebPackedProducer count/emit exactness (design section 2.2, lane L7)

#### reports and emits exactly the reserved rows for a real HTML page

- reports and emits exactly the reserved rows for a real HTML page
- A page with two absolutely-positioned boxes
   - Expected: counts.owner_records equals `counts.hit_shapes`
   - Expected: slice.scene_slot equals `1u32`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports and emits exactly the reserved rows for a real HTML page")
step("A page with two absolutely-positioned boxes")
val producer = WebPackedProducer(id_val: 1u32, html: L7_CORPUS_HTML, width: 100, height: 70, host_parent_id: DRAW_IR_V3_NO_ID, host_owner_id: DRAW_IR_V3_NO_ID)
val counts = producer.count(1u64, ui_scene_counts_zero())
expect(counts.commands).to_be_greater_than(0u32)
expect(counts.geometry).to_be_greater_than(0u32)
expect(counts.paint).to_be_greater_than(0u32)
expect(counts.hit_shapes).to_be_greater_than(0u32)
expect(counts.owner_records).to_equal(counts.hit_shapes)

val ranges = ui_scene_scan([counts])[0]
var draw = UiSceneNativeWriter.new(ranges)
var owners = UiSceneNativeOwnerWriter.new(ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(ranges.action_bindings)
val result = producer.emit(1u64, ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        expect(slice.scene_slot).to_equal(1u32)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
print "l7_web_producer_exactness commands={counts.commands} hit_shapes={counts.hit_shapes} owners={counts.owner_records}"
```

</details>

#### reports the same counts twice for the same page (count is repeatable)

- reports the same counts twice for the same page (count is repeatable)
   - Expected: first.commands equals `second.commands`
   - Expected: first.hit_shapes equals `second.hit_shapes`
   - Expected: first.owner_records equals `second.owner_records`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the same counts twice for the same page (count is repeatable)")
val producer = WebPackedProducer(id_val: 2u32, html: L7_CORPUS_HTML, width: 100, height: 70, host_parent_id: DRAW_IR_V3_NO_ID, host_owner_id: DRAW_IR_V3_NO_ID)
val first = producer.count(5u64, ui_scene_counts_zero())
val second = producer.count(5u64, ui_scene_counts_zero())
expect(first.commands).to_equal(second.commands)
expect(first.hit_shapes).to_equal(second.hit_shapes)
expect(first.owner_records).to_equal(second.owner_records)
```

</details>

### WebPackedProducer owner records (design section 2.4, gate b)

#### emits one owner record per hit-shape row, tagged WEB with the oracle's generation

- emits one owner record per hit-shape row, tagged WEB with the oracle's generation
   - Expected: slice.scene_slot equals `3u32`
   - Expected: true is false
   - Expected: hit_shapes.len() equals `records.len()`
   - Expected: rec.producer_kind equals `UI_PRODUCER_WEB`
   - Expected: rec.semantic_generation equals `0u32`
   - Expected: hit_shapes[i].component_id equals `rec.semantic_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits one owner record per hit-shape row, tagged WEB with the oracle's generation")
val producer = WebPackedProducer(id_val: 3u32, html: L7_CORPUS_HTML, width: 100, height: 70, host_parent_id: DRAW_IR_V3_NO_ID, host_owner_id: DRAW_IR_V3_NO_ID)
val counts = producer.count(1u64, ui_scene_counts_zero())
val ranges = ui_scene_scan([counts])[0]
var draw = UiSceneNativeWriter.new(ranges)
var owners = UiSceneNativeOwnerWriter.new(ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(ranges.action_bindings)
val result = producer.emit(1u64, ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        expect(slice.scene_slot).to_equal(3u32)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)

val hit_shapes = draw.hit_shapes_snapshot()
val records = owners.records_snapshot()
expect(hit_shapes.len()).to_equal(records.len())
expect(records.len()).to_be_greater_than(0)
var i = 0
while i < records.len():
    val rec = records[i]
    expect(rec.producer_kind).to_equal(UI_PRODUCER_WEB)
    expect(rec.semantic_generation).to_equal(0u32)
    expect(hit_shapes[i].component_id).to_equal(rec.semantic_id)
    i = i + 1
print "l7_web_producer_owners hit_shapes={hit_shapes.len()} owners={records.len()}"
```

</details>

### WebPackedProducer host_owner_id reparenting (cross-producer owner-chain wiring)

#### re-parents every owner record onto host_owner_id when nested

- re-parents every owner record onto host_owner_id when nested
   - Expected: records[i].parent_owner_id equals `host_owner_id`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-parents every owner record onto host_owner_id when nested")
val host_owner_id = 77u32
val producer = WebPackedProducer(id_val: 7u32, html: L7_CORPUS_HTML, width: 100, height: 70, host_parent_id: DRAW_IR_V3_NO_ID, host_owner_id: host_owner_id)
val counts = producer.count(1u64, ui_scene_counts_zero())
val ranges = ui_scene_scan([counts])[0]
var draw = UiSceneNativeWriter.new(ranges)
var owners = UiSceneNativeOwnerWriter.new(ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(ranges.action_bindings)
val result = producer.emit(1u64, ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        val records = owners.records_snapshot()
        expect(records.len()).to_be_greater_than(0)
        var i = 0
        while i < records.len():
            expect(records[i].parent_owner_id).to_equal(host_owner_id)
            i = i + 1
        print "l7_web_producer_host_owner_id owners={records.len()} parent={host_owner_id}"
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
```

</details>

### WebPackedProducer WebView nesting (design section 2.2 nesting rule, gate c/d)

#### re-parents the web root onto the host's WebView component and costs no extra arena allocation

- re-parents the web root onto the host's WebView component and costs no extra arena allocation
   - Expected: true is false
   - Expected: after_alloc equals `before_alloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-parents the web root onto the host's WebView component and costs no extra arena allocation")
val host_webview_component_id = 77u32
val capacity = _l7_generous_capacity()
val arena = UiSceneArena.new(capacity)
val before_alloc = arena.alloc_count()

val web = WebPackedProducer(id_val: 20u32, html: L7_CORPUS_HTML, width: 100, height: 70, host_parent_id: host_webview_component_id, host_owner_id: DRAW_IR_V3_NO_ID)
val web_counts = web.count(1u64, ui_scene_counts_zero())

var host_counts = ui_scene_counts_zero()
host_counts.commands = 1u32

val scanned = ui_scene_scan([host_counts, web_counts])
val child_ranges = scanned[1]

var draw = UiSceneNativeWriter.new(child_ranges)
var owners = UiSceneNativeOwnerWriter.new(child_ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(child_ranges.action_bindings)
val result = web.emit(1u64, child_ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        val commands = draw.commands_snapshot()
        var reparented = 0
        var i = 0
        while i < commands.len():
            if commands[i].parent_id == host_webview_component_id:
                reparented = reparented + 1
            i = i + 1
        expect(reparented).to_be_greater_than(0)

        val draw_committed = ui_scene_commit_draw_write(arena, draw, child_ranges)
        assert_true(draw_committed)
        val owner_committed = ui_scene_commit_owner_write(arena, owners, child_ranges.owner_records)
        assert_true(owner_committed)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)

val after_alloc = arena.alloc_count()
expect(after_alloc).to_equal(before_alloc)
print "l7_web_producer_nesting host_component={host_webview_component_id} alloc_before={before_alloc} alloc_after={after_alloc}"
```

</details>

### WebPackedProducer id rebasing under a non-zero assigned range (multi-producer composition)

#### keeps geometry_id/paint_id arena-absolute when scanned after a producer with non-zero counts

- keeps geometry_id/paint_id arena-absolute when scanned after a producer with non-zero counts
   - Expected: slice.scene_slot equals `6u32`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps geometry_id/paint_id arena-absolute when scanned after a producer with non-zero counts")
var dummy_counts = ui_scene_counts_zero()
dummy_counts.commands = 2u32
dummy_counts.geometry = 2u32
dummy_counts.paint = 2u32
dummy_counts.text_runs = 1u32
dummy_counts.glyphs = 3u32
dummy_counts.resources = 1u32
dummy_counts.path_spans = 1u32
dummy_counts.path_points = 2u32
dummy_counts.clips = 1u32
dummy_counts.transforms = 1u32
dummy_counts.hit_shapes = 1u32

val producer = WebPackedProducer(id_val: 6u32, html: L7_CORPUS_HTML, width: 100, height: 70, host_parent_id: DRAW_IR_V3_NO_ID, host_owner_id: DRAW_IR_V3_NO_ID)
val web_counts = producer.count(1u64, ui_scene_counts_zero())

val scanned = ui_scene_scan([dummy_counts, web_counts])
val web_ranges = scanned[1]
assert_true(web_ranges.geometry.start > 0u32)
assert_true(web_ranges.paint.start > 0u32)

var draw = UiSceneNativeWriter.new(web_ranges)
var owners = UiSceneNativeOwnerWriter.new(web_ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(web_ranges.action_bindings)
val result = producer.emit(1u64, web_ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        expect(slice.scene_slot).to_equal(6u32)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)

val commands = draw.commands_snapshot()
var checked_geometry = 0
var checked_paint = 0
var i = 0
while i < commands.len():
    if commands[i].geometry_id != DRAW_IR_V3_NO_ID:
        assert_true(commands[i].geometry_id >= web_ranges.geometry.start)
        checked_geometry = checked_geometry + 1
    if commands[i].paint_id != DRAW_IR_V3_NO_ID:
        assert_true(commands[i].paint_id >= web_ranges.paint.start)
        checked_paint = checked_paint + 1
    i = i + 1
assert_true(checked_geometry > 0)
assert_true(checked_paint > 0)
print "l7_web_producer_id_rebasing geometry_start={web_ranges.geometry.start} paint_start={web_ranges.paint.start} checked_geometry={checked_geometry} checked_paint={checked_paint}"
```

</details>

### WebPackedProducer parity with the v2 oracle (design section 9, gate d)

#### matches simple_web_layout_render_html_draw_ir + draw_ir_v2_to_v3 on commands, geometry and paint

- matches simple_web_layout_render_html_draw_ir + draw_ir_v2_to_v3 on commands, geometry and paint
   - Expected: slice.scene_slot equals `4u32`
   - Expected: true is false
   - Expected: produced_commands.len() equals `oracle_v3.commands.len()`
   - Expected: produced_geometry.len() equals `oracle_v3.geometry.xs.len()`
   - Expected: produced_geometry[i].x equals `oracle_v3.geometry.xs[i]`
   - Expected: produced_geometry[i].y equals `oracle_v3.geometry.ys[i]`
   - Expected: produced_geometry[i].width equals `oracle_v3.geometry.widths[i]`
   - Expected: produced_geometry[i].height equals `oracle_v3.geometry.heights[i]`
   - Expected: produced_paint.len() equals `oracle_v3.paint.fill_colors.len()`
   - Expected: produced_paint[i].fill_color equals `oracle_v3.paint.fill_colors[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches simple_web_layout_render_html_draw_ir + draw_ir_v2_to_v3 on commands, geometry and paint")
val oracle_v3 = draw_ir_v2_to_v3(simple_web_layout_render_html_draw_ir(L7_CORPUS_HTML, 100, 70))

val producer = WebPackedProducer(id_val: 4u32, html: L7_CORPUS_HTML, width: 100, height: 70, host_parent_id: DRAW_IR_V3_NO_ID, host_owner_id: DRAW_IR_V3_NO_ID)
val counts = producer.count(1u64, ui_scene_counts_zero())
val ranges = ui_scene_scan([counts])[0]
var draw = UiSceneNativeWriter.new(ranges)
var owners = UiSceneNativeOwnerWriter.new(ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(ranges.action_bindings)
val result = producer.emit(1u64, ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        expect(slice.scene_slot).to_equal(4u32)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)

val produced_commands = draw.commands_snapshot()
expect(produced_commands.len()).to_equal(oracle_v3.commands.len())

val produced_geometry = draw.geometry_snapshot()
expect(produced_geometry.len()).to_equal(oracle_v3.geometry.xs.len())
var i = 0
while i < produced_geometry.len():
    expect(produced_geometry[i].x).to_equal(oracle_v3.geometry.xs[i])
    expect(produced_geometry[i].y).to_equal(oracle_v3.geometry.ys[i])
    expect(produced_geometry[i].width).to_equal(oracle_v3.geometry.widths[i])
    expect(produced_geometry[i].height).to_equal(oracle_v3.geometry.heights[i])
    i = i + 1

val produced_paint = draw.paint_snapshot()
expect(produced_paint.len()).to_equal(oracle_v3.paint.fill_colors.len())
i = 0
while i < produced_paint.len():
    expect(produced_paint[i].fill_color).to_equal(oracle_v3.paint.fill_colors[i])
    i = i + 1
print "l7_web_producer_parity commands={produced_commands.len()} geometry={produced_geometry.len()} paint={produced_paint.len()}"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/ui_web_packed_producer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WebPackedProducer count/emit exactness (design section 2.2, lane L7), WebPackedProducer owner records (design section 2.4, gate b), WebPackedProducer host_owner_id reparenting (cross-producer owner-chain wiring), WebPackedProducer WebView nesting (design section 2.2 nesting rule, gate c/d), WebPackedProducer id rebasing under a non-zero assigned range (multi-producer composition), WebPackedProducer parity with the v2 oracle (design section 9, gate d).
- WebPackedProducer count/emit exactness (design section 2.2, lane L7)
- WebPackedProducer owner records (design section 2.4, gate b)
- WebPackedProducer host_owner_id reparenting (cross-producer owner-chain wiring)
- WebPackedProducer WebView nesting (design section 2.2 nesting rule, gate c/d)
- WebPackedProducer id rebasing under a non-zero assigned range (multi-producer composition)
- WebPackedProducer parity with the v2 oracle (design section 9, gate d)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `90992f35c78111741661d5ede38386af0bad427f1a9e4b296bacd68fed42ec26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90992f35c78111741661d5ede38386af0bad427f1a9e4b296bacd68fed42ec26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90992f35c78111741661d5ede38386af0bad427f1a9e4b296bacd68fed42ec26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/ui_web_packed_producer_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/ui_web_packed_producer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/ui_web_packed_producer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/ui_web_packed_producer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/ui_web_packed_producer_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports and emits exactly the reserved rows for a real HTML page' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_web_packed_producer_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the same counts twice for the same page (count is repeatable)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_web_packed_producer_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits one owner record per hit-shape row, tagged WEB with the oracle's generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
