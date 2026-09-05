# Global Menubar Specification

> Tests covering WmPackedProducer global menubar segment (design section 6, gate a), WmPackedProducer menubar focus switch (design section 6, gate b), WmPackedProducer menu action dispatch (design section 6, gate c), WmPackedProducer background resolution (design section 6, gate d).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Global Menubar Specification

## Scenarios

### WmPackedProducer global menubar segment (design section 6, gate a)

#### emits exactly one GROUP whose children are the WM_MENUBAR_MAX_ITEMS menubar items

- emits exactly one GROUP whose children are the WM_MENUBAR_MAX_ITEMS menubar items
   - Expected: menubar_group_count equals `1`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits exactly one GROUP whose children are the WM_MENUBAR_MAX_ITEMS menubar items")
var menu_registry = AppMenuRegistry.new()
menu_registry.register(1u32, 1u32, DRAW_IR_V3_NO_ID, ["File", "Edit"], DRAW_IR_V3_NO_ID)
val producer = _wm_producer(1u32, menu_registry, 1u32, shared_wm_background_color(0xFF112233u32))
val counts = producer.count(1u64, ui_scene_counts_zero())
val ranges = ui_scene_scan([counts])[0]
var draw = UiSceneNativeWriter.new(ranges)
var owners = UiSceneNativeOwnerWriter.new(ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(ranges.action_bindings)
val result = producer.emit(1u64, ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        val commands = draw.commands_snapshot()
        var menubar_group_count = 0
        var gi = 0
        while gi < commands.len():
            if commands[gi].kind == DRAW_IR_V3_KIND_GROUP:
                var child_count = 0
                var ci = 0
                while ci < commands.len():
                    if commands[ci].parent_id == commands[gi].component_id:
                        child_count = child_count + 1
                    ci = ci + 1
                if child_count.to_u32() == WM_MENUBAR_MAX_ITEMS:
                    menubar_group_count = menubar_group_count + 1
            gi = gi + 1
        expect(menubar_group_count).to_equal(1)
        print "l8_wm_menubar_group_count commands={commands.len()} menubar_groups={menubar_group_count}"
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
```

</details>

### WmPackedProducer menubar focus switch (design section 6, gate b)

#### keeps every table's reserved count invariant and only menubar action content changes

- keeps every table's reserved count invariant and only menubar action content changes
   - Expected: counts_a.commands equals `counts_b.commands`
   - Expected: counts_a.geometry equals `counts_b.geometry`
   - Expected: counts_a.paint equals `counts_b.paint`
   - Expected: counts_a.hit_shapes equals `counts_b.hit_shapes`
   - Expected: counts_a.owner_records equals `counts_b.owner_records`
   - Expected: counts_a.action_bindings equals `counts_b.action_bindings`
   - Expected: geom_a[0].x equals `geom_b[0].x`
   - Expected: geom_a[0].width equals `geom_b[0].width`
   - Expected: paint_a[0].fill_color equals `paint_b[0].fill_color`
   - Expected: bindings_a.len() equals `bindings_b.len()`
   - Expected: bindings_a[0].app_id equals `1u32`
   - Expected: bindings_b[0].app_id equals `2u32`
   - Expected: true is false
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps every table's reserved count invariant and only menubar action content changes")
var menu_registry = AppMenuRegistry.new()
menu_registry.register(1u32, 1u32, DRAW_IR_V3_NO_ID, ["File", "Edit"], DRAW_IR_V3_NO_ID)
menu_registry.register(2u32, 1u32, DRAW_IR_V3_NO_ID, ["New", "Open", "Save", "Close"], DRAW_IR_V3_NO_ID)

val producer_a = _wm_producer(1u32, menu_registry, 1u32, shared_wm_background_color(0xFF112233u32))
val producer_b = _wm_producer(2u32, menu_registry, 2u32, shared_wm_background_color(0xFF112233u32))

val counts_a = producer_a.count(1u64, ui_scene_counts_zero())
val counts_b = producer_b.count(1u64, ui_scene_counts_zero())
expect(counts_a.commands).to_equal(counts_b.commands)
expect(counts_a.geometry).to_equal(counts_b.geometry)
expect(counts_a.paint).to_equal(counts_b.paint)
expect(counts_a.hit_shapes).to_equal(counts_b.hit_shapes)
expect(counts_a.owner_records).to_equal(counts_b.owner_records)
expect(counts_a.action_bindings).to_equal(counts_b.action_bindings)

val ranges_a = ui_scene_scan([counts_a])[0]
var draw_a = UiSceneNativeWriter.new(ranges_a)
var owners_a = UiSceneNativeOwnerWriter.new(ranges_a.owner_records)
var actions_a = UiSceneNativeActionWriter.new(ranges_a.action_bindings)
val result_a = producer_a.emit(1u64, ranges_a, draw_a, owners_a, actions_a)

val ranges_b = ui_scene_scan([counts_b])[0]
var draw_b = UiSceneNativeWriter.new(ranges_b)
var owners_b = UiSceneNativeOwnerWriter.new(ranges_b.owner_records)
var actions_b = UiSceneNativeActionWriter.new(ranges_b.action_bindings)
val result_b = producer_b.emit(1u64, ranges_b, draw_b, owners_b, actions_b)

match result_a:
    UiSceneEmitResult.Emitted(slice_a):
        match result_b:
            UiSceneEmitResult.Emitted(slice_b):
                val geom_a = draw_a.geometry_snapshot()
                val geom_b = draw_b.geometry_snapshot()
                expect(geom_a[0].x).to_equal(geom_b[0].x)
                expect(geom_a[0].width).to_equal(geom_b[0].width)
                val paint_a = draw_a.paint_snapshot()
                val paint_b = draw_b.paint_snapshot()
                expect(paint_a[0].fill_color).to_equal(paint_b[0].fill_color)

                val bindings_a = actions_a.bindings_snapshot()
                val bindings_b = actions_b.bindings_snapshot()
                expect(bindings_a.len()).to_equal(bindings_b.len())
                expect(bindings_a[0].app_id).to_equal(1u32)
                expect(bindings_b[0].app_id).to_equal(2u32)
                print "l8_wm_menubar_switch bindings={bindings_a.len()} app_a={bindings_a[0].app_id} app_b={bindings_b[0].app_id}"
            UiSceneEmitResult.Refused(receipt):
                expect(true).to_equal(false)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
```

</details>

### WmPackedProducer menu action dispatch (design section 6, gate c)

#### validates a live binding and refuses a stale menu_revision

- validates a live binding and refuses a stale menu_revision
   - Expected: ok.accepted is true
   - Expected: stale.accepted is false
   - Expected: stale.reason equals `UI_SCENE_DISPATCH_REFUSE_STALE_MENU_REVISION`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates a live binding and refuses a stale menu_revision")
var menu_registry = AppMenuRegistry.new()
menu_registry.register(1u32, 1u32, DRAW_IR_V3_NO_ID, ["File", "Edit"], DRAW_IR_V3_NO_ID)
val producer = _wm_producer(1u32, menu_registry, 1u32, shared_wm_background_color(0xFF112233u32))
val counts = producer.count(1u64, ui_scene_counts_zero())
val ranges = ui_scene_scan([counts])[0]
var draw = UiSceneNativeWriter.new(ranges)
var owners = UiSceneNativeOwnerWriter.new(ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(ranges.action_bindings)
val result = producer.emit(1u64, ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        val bindings = actions.bindings_snapshot()
        expect(bindings.len()).to_be_greater_than(0)
        val live = bindings[0]

        val ok = ui_scene_validate_menu_action_dispatch(live, live.app_generation, live.menu_revision)
        expect(ok.accepted).to_equal(true)

        val stale = ui_scene_validate_menu_action_dispatch(live, live.app_generation, live.menu_revision + 1u32)
        expect(stale.accepted).to_equal(false)
        expect(stale.reason).to_equal(UI_SCENE_DISPATCH_REFUSE_STALE_MENU_REVISION)
        print "l8_wm_menu_dispatch ok={ok.accepted} stale_reason={stale.reason}"
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
```

</details>

### WmPackedProducer background resolution (design section 6, gate d)

#### paints the resolved color for a color background

- paints the resolved color for a color background
   - Expected: paint[0].fill_color equals `0xFFAABBCCu32`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("paints the resolved color for a color background")
var menu_registry = AppMenuRegistry.new()
val producer = _wm_producer(1u32, menu_registry, DRAW_IR_V3_NO_ID, shared_wm_background_color(0xFFAABBCCu32))
val counts = producer.count(1u64, ui_scene_counts_zero())
val ranges = ui_scene_scan([counts])[0]
var draw = UiSceneNativeWriter.new(ranges)
var owners = UiSceneNativeOwnerWriter.new(ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(ranges.action_bindings)
val result = producer.emit(1u64, ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        val paint = draw.paint_snapshot()
        expect(paint[0].fill_color).to_equal(0xFFAABBCCu32)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
```

</details>

#### paints the loud unresolved-marker color for an unsupported background kind, never a silent substitute

- paints the loud unresolved-marker color for an unsupported background kind, never a silent substitute
   - Expected: paint[0].fill_color equals `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("paints the loud unresolved-marker color for an unsupported background kind, never a silent substitute")
var menu_registry = AppMenuRegistry.new()
val bogus_background = BackgroundSpec(kind: "not-a-real-kind", color: 0xFF000000u32, source: "", fit: "")
val producer = _wm_producer(1u32, menu_registry, DRAW_IR_V3_NO_ID, bogus_background)
val counts = producer.count(1u64, ui_scene_counts_zero())
val ranges = ui_scene_scan([counts])[0]
var draw = UiSceneNativeWriter.new(ranges)
var owners = UiSceneNativeOwnerWriter.new(ranges.owner_records)
var actions = UiSceneNativeActionWriter.new(ranges.action_bindings)
val result = producer.emit(1u64, ranges, draw, owners, actions)
match result:
    UiSceneEmitResult.Emitted(slice):
        val paint = draw.paint_snapshot()
        expect(paint[0].fill_color).to_equal(WM_BACKGROUND_UNRESOLVED_MARKER_COLOR)
        print "l8_wm_background_unresolved marker={paint[0].fill_color}"
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/ui/global_menubar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WmPackedProducer global menubar segment (design section 6, gate a), WmPackedProducer menubar focus switch (design section 6, gate b), WmPackedProducer menu action dispatch (design section 6, gate c), WmPackedProducer background resolution (design section 6, gate d).
- WmPackedProducer global menubar segment (design section 6, gate a)
- WmPackedProducer menubar focus switch (design section 6, gate b)
- WmPackedProducer menu action dispatch (design section 6, gate c)
- WmPackedProducer background resolution (design section 6, gate d)

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5eefda048236ae3006ac4d33f38f1137420c92d876e20e9ed8867f1a2c1cbdd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5eefda048236ae3006ac4d33f38f1137420c92d876e20e9ed8867f1a2c1cbdd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5eefda048236ae3006ac4d33f38f1137420c92d876e20e9ed8867f1a2c1cbdd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/ui/global_menubar_spec.spl
mirror: doc/06_spec/02_integration/ui/global_menubar_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/ui/global_menubar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/ui/global_menubar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/ui/global_menubar_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/ui/global_menubar_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits exactly one GROUP whose children are the WM_MENUBAR_MAX_ITEMS menubar items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/ui/global_menubar_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every table's reserved count invariant and only menubar action content changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/ui/global_menubar_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates a live binding and refuses a stale menu_revision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
