# Editor Panels Facade Specification

> 1. var hierarchy = HierarchyPanel new

<!-- sdn-diagram:id=editor_panels_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_panels_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_panels_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_panels_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Panels Facade Specification

## Scenarios

### nogc_async_mut editor panels facade

#### re-exports hierarchy, asset browser, mixer, and inspector panel behavior

1. var hierarchy = HierarchyPanel new
2. HierarchyEntry
3. HierarchyEntry
   - Expected: hierarchy.entry_count() equals `2`
   - Expected: hierarchy.visible_entries().len() equals `1`
4. hierarchy toggle expand
   - Expected: hierarchy.visible_entries().len() equals `2`
5. hierarchy select node
   - Expected: detect_asset_type("hero.png") equals `AssetType.TextureAsset`
6. var browser = AssetBrowserPanel new
7. AssetEntry file
8. AssetEntry directory
   - Expected: browser.entry_count() equals `2`
9. browser set search
   - Expected: browser.filtered_entries().len() equals `1`
10. var mixer = AudioMixerPanel new
11. MixerChannel
12. mixer set volume
   - Expected: mixer.channel_count() equals `1`
   - Expected: mixer.master_volume equals `1.0`
13. var inspector = InspectorPanel new
   - Expected: inspector.section_count() equals `1`
14. inspector toggle section
   - Expected: inspector.sections[0].expanded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/nogc_async_mut/editor/panels/editor_panels_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut editor panels facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
