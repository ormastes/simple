# Unified Packed Scene Nesting Specification

> Tests covering Unified packed UI scene nested composition (WM->GUI->Web, real producer output).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified Packed Scene Nesting Specification

## Scenarios

### Unified packed UI scene nested composition (WM->GUI->Web, real producer output)

#### routes a click on the Web element through GUI's WebView-host owner to WM's window owner

- routes a click on the Web element through GUI's WebView-host owner to WM's window owner
- Pass 1: emit WM for real, read back its window owner's absolute index
   - Expected: true is false
- Pass 2: emit GUI nested under WM's window owner, read back its WebView-host owner's absolute index
   - Expected: records.len() equals `1`
   - Expected: records[0].parent_owner_id equals `wm_window_owner_abs`
   - Expected: true is false
- Pass 3: emit Web nested under GUI's WebView-host owner
   - Expected: true is false
- Verify owner-table ranges match emission order before trusting plain-push combining
- Combine into one scene + one owner array (scan order), rebasing each producer's local component_id/semantic_id space
   - Expected: receipt.accepted is true
   - Expected: receipt.owner_chain.len() equals `3`
   - Expected: receipt.owner_chain[1] equals `gui_webview_owner_abs`
   - Expected: receipt.owner_chain[2] equals `wm_window_owner_abs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 113 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes a click on the Web element through GUI's WebView-host owner to WM's window owner")
val wm = _ns_wm_producer()
val gui_placeholder = _ns_gui_producer(DRAW_IR_V3_NO_ID)
val web_placeholder = _ns_web_producer(DRAW_IR_V3_NO_ID)

# host_owner_id/host_parent_id affect owner-record CONTENT only,
# never row COUNTS (verified: _gui_counts_of/_web_counts_of never
# read either field) -- so counts computed from placeholders are
# valid for the real, correctly-nested producers built below.
val wm_counts = wm.count(1u64, ui_scene_counts_zero())
val gui_counts = gui_placeholder.count(1u64, ui_scene_counts_zero())
val web_counts = web_placeholder.count(1u64, ui_scene_counts_zero())
val scanned = ui_scene_scan([wm_counts, gui_counts, web_counts])
val wm_ranges = scanned[0]
val gui_ranges = scanned[1]
val web_ranges = scanned[2]

step("Pass 1: emit WM for real, read back its window owner's absolute index")
var wm_draw = UiSceneNativeWriter.new(wm_ranges)
var wm_owners = UiSceneNativeOwnerWriter.new(wm_ranges.owner_records)
var wm_actions = UiSceneNativeActionWriter.new(wm_ranges.action_bindings)
val wm_result = wm.emit(1u64, wm_ranges, wm_draw, wm_owners, wm_actions)
var wm_window_owner_abs = DRAW_IR_V3_NO_ID
match wm_result:
    UiSceneEmitResult.Emitted(slice):
        val target_semantic_id = wm_packed_producer_window_owner_semantic_id(wm, 0u32)
        val records = wm_owners.records_snapshot()
        var i = 0
        while i < records.len():
            if records[i].semantic_id == target_semantic_id:
                wm_window_owner_abs = wm_ranges.owner_records.start + i.to_u32()
            i = i + 1
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
assert_true(wm_window_owner_abs != DRAW_IR_V3_NO_ID)

step("Pass 2: emit GUI nested under WM's window owner, read back its WebView-host owner's absolute index")
val gui = _ns_gui_producer(wm_window_owner_abs)
var gui_draw = UiSceneNativeWriter.new(gui_ranges)
var gui_owners = UiSceneNativeOwnerWriter.new(gui_ranges.owner_records)
var gui_actions = UiSceneNativeActionWriter.new(gui_ranges.action_bindings)
val gui_result = gui.emit(1u64, gui_ranges, gui_draw, gui_owners, gui_actions)
var gui_webview_owner_abs = DRAW_IR_V3_NO_ID
match gui_result:
    UiSceneEmitResult.Emitted(slice):
        val records = gui_owners.records_snapshot()
        expect(records.len()).to_equal(1)
        expect(records[0].parent_owner_id).to_equal(wm_window_owner_abs)
        gui_webview_owner_abs = gui_ranges.owner_records.start
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)
assert_true(gui_webview_owner_abs != DRAW_IR_V3_NO_ID)

step("Pass 3: emit Web nested under GUI's WebView-host owner")
val web = _ns_web_producer(gui_webview_owner_abs)
var web_draw = UiSceneNativeWriter.new(web_ranges)
var web_owners = UiSceneNativeOwnerWriter.new(web_ranges.owner_records)
var web_actions = UiSceneNativeActionWriter.new(web_ranges.action_bindings)
val web_result = web.emit(1u64, web_ranges, web_draw, web_owners, web_actions)
match web_result:
    UiSceneEmitResult.Emitted(slice):
        expect(web_owners.records_snapshot().len()).to_be_greater_than(0)
    UiSceneEmitResult.Refused(receipt):
        expect(true).to_equal(false)

step("Verify owner-table ranges match emission order before trusting plain-push combining")
# combined_owners below is built by pushing each producer's records
# in scan order; that only reproduces a real committed UiSceneArena
# if each producer's assigned owner_records range starts exactly
# where the previous producer's rows end -- assert it instead of
# trusting the coincidence.
val wm_owner_count = wm_owners.records_snapshot().len().to_u32()
val gui_owner_count = gui_owners.records_snapshot().len().to_u32()
val web_owner_count = web_owners.records_snapshot().len().to_u32()
assert_true(wm_ranges.owner_records.start == 0u32)
assert_true(gui_ranges.owner_records.start == wm_ranges.owner_records.start + wm_owner_count)
assert_true(web_ranges.owner_records.start == gui_ranges.owner_records.start + gui_owner_count)

step("Combine into one scene + one owner array (scan order), rebasing each producer's local component_id/semantic_id space")
var combined = draw_ir_v3_empty_scene(1u32, 1u32)
val wm_id_offset = combined.commands.len().to_u32()
combined = _ns_append_writer_output(combined, wm_draw, wm_id_offset)
val gui_id_offset = combined.commands.len().to_u32()
combined = _ns_append_writer_output(combined, gui_draw, gui_id_offset)
val web_id_offset = combined.commands.len().to_u32()
combined = _ns_append_writer_output(combined, web_draw, web_id_offset)

var combined_owners: [UiOwnerRecord] = []
for rec in wm_owners.records_snapshot():
    var r = rec
    r.semantic_id = _ns_rebase_component(rec.semantic_id, wm_id_offset)
    combined_owners.push(r)
for rec in gui_owners.records_snapshot():
    var r = rec
    r.semantic_id = _ns_rebase_component(rec.semantic_id, gui_id_offset)
    combined_owners.push(r)
for rec in web_owners.records_snapshot():
    var r = rec
    r.semantic_id = _ns_rebase_component(rec.semantic_id, web_id_offset)
    combined_owners.push(r)

val resolved = draw_ir_v3_group_resolve(combined, draw_ir_v3_port_surface_state_empty())
val receipt = ui_scene_route_event(combined, resolved, combined_owners, 10, 10)

expect(receipt.accepted).to_equal(true)
expect(receipt.owner_chain.len()).to_equal(3)
val web_owner_start = web_ranges.owner_records.start
assert_true(receipt.owner_chain[0] >= web_owner_start)
assert_true(receipt.owner_chain[0] < web_owner_start + web_owner_count)
expect(receipt.owner_chain[1]).to_equal(gui_webview_owner_abs)
expect(receipt.owner_chain[2]).to_equal(wm_window_owner_abs)
print "ns_nested_route chain=[{receipt.owner_chain[0]},{receipt.owner_chain[1]},{receipt.owner_chain[2]}] wm_window={wm_window_owner_abs} gui_host={gui_webview_owner_abs}"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/ui/unified_packed_scene_nesting_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Unified packed UI scene nested composition (WM->GUI->Web, real producer output).
- Unified packed UI scene nested composition (WM->GUI->Web, real producer output)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `4f6617af2a036e18f5e27f02dfa255afbe3652f28eb6bd04b529d0a925c15a7a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f6617af2a036e18f5e27f02dfa255afbe3652f28eb6bd04b529d0a925c15a7a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f6617af2a036e18f5e27f02dfa255afbe3652f28eb6bd04b529d0a925c15a7a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/02_integration/ui/unified_packed_scene_nesting_spec.spl
mirror: doc/06_spec/02_integration/ui/unified_packed_scene_nesting_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/ui/unified_packed_scene_nesting_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/ui/unified_packed_scene_nesting_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/ui/unified_packed_scene_nesting_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/ui/unified_packed_scene_nesting_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a click on the Web element through GUI's WebView-host owner to WM's window owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
