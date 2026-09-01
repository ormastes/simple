# Editor Panels Facade Specification

> Tests covering gc_async_mut editor panels facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Panels Facade Specification

## Scenarios

### gc_async_mut editor panels facade

#### re-exports hierarchy, asset browser, mixer, and inspector panel behavior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports hierarchy, asset browser, mixer, and inspector panel behavior
   - Expected: hierarchy.entry_count() equals `2`
   - Expected: hierarchy.visible_entries().len() equals `1`
   - Expected: hierarchy.visible_entries().len() equals `2`
   - Expected: detect_asset_type("hero.png") equals `AssetType.TextureAsset`
   - Expected: browser.entry_count() equals `2`
   - Expected: browser.filtered_entries().len() equals `1`
   - Expected: mixer.channel_count() equals `1`
   - Expected: mixer.master_volume equals `1.0`
   - Expected: inspector.section_count() equals `1`
   - Expected: inspector.sections[0].expanded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports hierarchy, asset browser, mixer, and inspector panel behavior")
val root_id = NodeId(id: 1)
val child_id = NodeId(id: 2)
var hierarchy = HierarchyPanel.new()
hierarchy.rebuild([
    HierarchyEntry(node_id: root_id, name: "Root", depth: 0, expanded: false, has_children: true, selected: false),
    HierarchyEntry(node_id: child_id, name: "Child", depth: 1, expanded: true, has_children: false, selected: false)
])
expect(hierarchy.entry_count()).to_equal(2)
expect(hierarchy.visible_entries().len()).to_equal(1)
hierarchy.toggle_expand(root_id)
expect(hierarchy.visible_entries().len()).to_equal(2)
hierarchy.select_node(child_id)

expect(detect_asset_type("hero.png")).to_equal(AssetType.TextureAsset)
var browser = AssetBrowserPanel.new("/assets")
browser.set_entries([
    AssetEntry.file("hero.png", "/assets/hero.png", AssetType.TextureAsset, 32),
    AssetEntry.directory("scenes", "/assets/scenes")
])
expect(browser.entry_count()).to_equal(2)
browser.set_search("hero")
expect(browser.filtered_entries().len()).to_equal(1)

var mixer = AudioMixerPanel.new()
mixer.set_channels([
    MixerChannel(group_name: "master", display_name: "Master", volume: 1.0, muted: false, solo: false, level_left: 0.0, level_right: 0.0, depth: 0)
])
mixer.set_volume("master", 2.0)
expect(mixer.channel_count()).to_equal(1)
expect(mixer.master_volume).to_equal(1.0)

val field = PropertyField(component_name: "Transform", property_name: "x", display_name: "X", prop_type: PropertyType.FloatProp, value_text: "1", editable: true)
val section = ComponentSection(name: "Transform", expanded: true, fields: [field])
var inspector = InspectorPanel.new()
inspector.sections = [section]
expect(inspector.section_count()).to_equal(1)
inspector.toggle_section("Transform")
expect(inspector.sections[0].expanded).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/editor/panels/editor_panels_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut editor panels facade.
- gc_async_mut editor panels facade

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a14afd99a655a49693b8e2a11934fd105e22038eaf94109224514eeaf0381c01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a14afd99a655a49693b8e2a11934fd105e22038eaf94109224514eeaf0381c01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a14afd99a655a49693b8e2a11934fd105e22038eaf94109224514eeaf0381c01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/editor/panels/editor_panels_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/editor/panels/editor_panels_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/editor/panels/editor_panels_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/editor/panels/editor_panels_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/editor/panels/editor_panels_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/editor/panels/editor_panels_facade_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports hierarchy, asset browser, mixer, and inspector panel behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
