# Scene Node Specification

> Tests covering SceneNode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scene Node Specification

## Scenarios

### SceneNode

#### creates nodes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates nodes")
val node = SceneNode.new("test_node")
check(node.name == "test_node")
check(node.visible == true)
```

</details>

#### handles parent-child relationships

- handles parent-child relationships


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles parent-child relationships")
val parent = SceneNode.new("parent")
val child = SceneNode.new("child")
parent.add_child(child)
check(parent.get_children().len() == 1)
```

</details>

#### handles transforms

- handles transforms


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles transforms")
val node = SceneNode.new("node_with_transform")
val transform = node.get_transform()
check(transform.x == 0.0)
check(transform.y == 0.0)
check(transform.z == 0.0)
```

</details>

#### handles visibility

- handles visibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles visibility")
val node = SceneNode.new("visible_node")
check(node.is_visible() == true)
node.set_visible(false)
check(node.is_visible() == false)
```

</details>

#### traverses scene graph

- traverses scene graph


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traverses scene graph")
val root = SceneNode.new("root")
val child1 = SceneNode.new("child1")
val child2 = SceneNode.new("child2")
root.add_child(child1)
root.add_child(child2)
var children = root.get_children()
check(children.len() == 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SceneNode.
- SceneNode

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aaa92bbea86b769a87afc954d71cfca37a8220e5231ddd66ba8d2bd7424e1c3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aaa92bbea86b769a87afc954d71cfca37a8220e5231ddd66ba8d2bd7424e1c3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aaa92bbea86b769a87afc954d71cfca37a8220e5231ddd66ba8d2bd7424e1c3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates nodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles parent-child relationships' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles transforms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
