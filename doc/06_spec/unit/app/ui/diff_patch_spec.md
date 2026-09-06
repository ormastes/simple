# Diff Patch Specification

> Tests covering diff_trees identical, diff_trees property changes, diff_trees kind changes, diff_trees layout changes, diff_trees visibility changes, diff_trees child changes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diff Patch Specification

## Scenarios

### diff_trees identical

#### produces empty patch list for identical trees

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces empty patch list for identical trees


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces empty patch list for identical trees")
val old_tree = WidgetNode.new("id1", "text")
val new_tree = WidgetNode.new("id1", "text")
val patches = diff_trees(old_tree, new_tree)
expect patches.len() to_equal 0
```

</details>

### diff_trees property changes

#### produces UpdateProp patch for changed property

- produces UpdateProp patch for changed property


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces UpdateProp patch for changed property")
var old_node = WidgetNode.new("prop1", "text")
old_node = old_node.set_prop("content", "Hello")
var new_node = WidgetNode.new("prop1", "text")
new_node = new_node.set_prop("content", "World")
val patches = diff_trees(old_node, new_node)
expect patches.len() to_equal 1
val patch = patches[0]
expect patch.kind to_equal PatchKind.UpdateProp
expect patch.prop_key to_equal "content"
expect patch.prop_value to_equal "World"
```

</details>

#### produces RemoveProp patch for removed property

- produces RemoveProp patch for removed property


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces RemoveProp patch for removed property")
var old_node = WidgetNode.new("prop2", "text")
old_node = old_node.set_prop("content", "Hello")
old_node = old_node.set_prop("color", "red")
var new_node = WidgetNode.new("prop2", "text")
new_node = new_node.set_prop("content", "Hello")
# "color" prop is absent in new_node
val patches = diff_trees(old_node, new_node)
var found_remove = false
for patch in patches:
    if patch.kind == PatchKind.RemoveProp and patch.prop_key == "color":
        found_remove = true
expect found_remove to_equal true
```

</details>

#### produces UpdateProp patch for added property

- produces UpdateProp patch for added property


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces UpdateProp patch for added property")
var old_node = WidgetNode.new("prop3", "text")
old_node = old_node.set_prop("content", "Hello")
var new_node = WidgetNode.new("prop3", "text")
new_node = new_node.set_prop("content", "Hello")
new_node = new_node.set_prop("color", "blue")
val patches = diff_trees(old_node, new_node)
var found_update = false
for patch in patches:
    if patch.kind == PatchKind.UpdateProp and patch.prop_key == "color":
        found_update = true
        expect patch.prop_value to_equal "blue"
expect found_update to_equal true
```

</details>

### diff_trees kind changes

#### produces ReplaceNode patch for changed kind

- produces ReplaceNode patch for changed kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces ReplaceNode patch for changed kind")
val old_node = WidgetNode.new("kind1", "text")
val new_node = WidgetNode.new("kind1", "button")
val patches = diff_trees(old_node, new_node)
expect patches.len() to_equal 1
expect patches[0].kind to_equal PatchKind.ReplaceNode
```

</details>

### diff_trees layout changes

#### produces UpdateLayout patch for changed layout

- produces UpdateLayout patch for changed layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces UpdateLayout patch for changed layout")
var old_node = WidgetNode.new("lay1", "panel")
old_node = old_node.set_layout("vbox")
var new_node = WidgetNode.new("lay1", "panel")
new_node = new_node.set_layout("hbox")
val patches = diff_trees(old_node, new_node)
var found_layout = false
for patch in patches:
    if patch.kind == PatchKind.UpdateLayout:
        found_layout = true
expect found_layout to_equal true
```

</details>

### diff_trees visibility changes

#### produces UpdateVisibility patch for changed visibility

- produces UpdateVisibility patch for changed visibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces UpdateVisibility patch for changed visibility")
var old_node = WidgetNode.new("vis1", "panel")
var new_node = WidgetNode.new("vis1", "panel")
new_node = new_node.set_visible(false)
val patches = diff_trees(old_node, new_node)
var found_vis = false
for patch in patches:
    if patch.kind == PatchKind.UpdateVisibility:
        found_vis = true
expect found_vis to_equal true
```

</details>

### diff_trees child changes

#### produces InsertChild patch for added child

- produces InsertChild patch for added child


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces InsertChild patch for added child")
val old_node = WidgetNode.new("par1", "panel")
var new_node = WidgetNode.new("par1", "panel")
val child = WidgetNode.new("par1_child", "text")
new_node = new_node.add_child(child)
val patches = diff_trees(old_node, new_node)
var found_insert = false
for patch in patches:
    if patch.kind == PatchKind.InsertChild:
        found_insert = true
        expect patch.target_id to_equal "par1_child"
expect found_insert to_equal true
```

</details>

#### produces RemoveChild patch for removed child

- produces RemoveChild patch for removed child


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces RemoveChild patch for removed child")
var old_node = WidgetNode.new("par2", "panel")
val child = WidgetNode.new("par2_child", "text")
old_node = old_node.add_child(child)
val new_node = WidgetNode.new("par2", "panel")
val patches = diff_trees(old_node, new_node)
var found_remove = false
for patch in patches:
    if patch.kind == PatchKind.RemoveChild:
        found_remove = true
        expect patch.target_id to_equal "par2_child"
expect found_remove to_equal true
```

</details>

#### produces no patches when children are identical

- produces no patches when children are identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces no patches when children are identical")
var old_node = WidgetNode.new("par3", "panel")
val child_old = WidgetNode.new("par3_kid", "text")
old_node = old_node.add_child(child_old)
var new_node = WidgetNode.new("par3", "panel")
val child_new = WidgetNode.new("par3_kid", "text")
new_node = new_node.add_child(child_new)
val patches = diff_trees(old_node, new_node)
expect patches.len() to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/diff_patch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering diff_trees identical, diff_trees property changes, diff_trees kind changes, diff_trees layout changes, diff_trees visibility changes, diff_trees child changes.
- diff_trees identical
- diff_trees property changes
- diff_trees kind changes
- diff_trees layout changes
- diff_trees visibility changes
- diff_trees child changes

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c7655a5a56d63821bb37dd22b2e8804bfa13a3ba130caaaa43ba744bf7a29add`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7655a5a56d63821bb37dd22b2e8804bfa13a3ba130caaaa43ba744bf7a29add`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7655a5a56d63821bb37dd22b2e8804bfa13a3ba130caaaa43ba744bf7a29add`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/diff_patch_spec.spl
mirror: doc/06_spec/unit/app/ui/diff_patch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/diff_patch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/diff_patch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/diff_patch_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces empty patch list for identical trees' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/diff_patch_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces UpdateProp patch for changed property' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/diff_patch_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces RemoveProp patch for removed property' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
