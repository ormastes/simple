# Claude Full Native Yoga Layout

> Purpose: should resolve values, edges, and axis helpers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Native Yoga Layout

Purpose: should resolve values, edges, and axis helpers

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should resolve values, edges, and axis helpers
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Native Yoga Layout

Checks Yoga layout parity for Node tree/style/layout behavior used by Ink.

## Scenarios

### Claude full native yoga layout

#### should resolve values, edges, and axis helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should resolve values, edges, and axis helpers
- Verify: should resolve values, edges, and axis helpers
- Resolve point, percent, and edge precedence
   - Expected: resolveValue(pointValue(10), 100) equals `10`
   - Expected: resolveValue(percentValue(25), 200) equals `50`
   - Expected: resolveEdge(edges, EDGE_LEFT, 100, false) equals `3`
   - Expected: resolveEdge(edges, EDGE_TOP, 100, false) equals `1`
   - Expected: isRow("row") is true
   - Expected: crossAxis("row") equals `column`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve values, edges, and axis helpers")
step("Verify: should resolve values, edges, and axis helpers")
# @req: REQ-TOOLS-Inde-001
step("Resolve point, percent, and edge precedence")
expect(resolveValue(pointValue(10), 100)).to_equal(10)  # oracle: value fixed by the spec contract
expect(resolveValue(percentValue(25), 200)).to_equal(50)  # oracle: value fixed by the spec contract
val edges = defaultEdges()
edges[EDGE_HORIZONTAL] = pointValue(3)
edges[EDGE_ALL] = pointValue(1)
expect(resolveEdge(edges, EDGE_LEFT, 100, false)).to_equal(3)  # oracle: value fixed by the spec contract
expect(resolveEdge(edges, EDGE_TOP, 100, false)).to_equal(1)  # oracle: value fixed by the spec contract
expect(isRow("row")).to_equal(true)
expect(crossAxis("row")).to_equal("column")
```

</details>

#### should create config and loader surfaces

- should create config and loader surfaces
- Verify: should create config and loader surfaces
- Configure Yoga
   - Expected: config.pointScaleFactor equals `2`
   - Expected: config.getErrata() equals `classic`
   - Expected: loadYoga().hasNode is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create config and loader surfaces")
step("Verify: should create config and loader surfaces")
# @req: REQ-TOOLS-Inde-001
step("Configure Yoga")
val config = createConfig()
config.setPointScaleFactor(2)
config.setErrata("classic")
config.setUseWebDefaults(true)
expect(config.pointScaleFactor).to_equal(2)  # oracle: value fixed by the spec contract
expect(config.getErrata()).to_equal("classic")
expect(loadYoga().hasNode).to_equal(true)
```

</details>

#### should maintain tree relationships and dirty state

- should maintain tree relationships and dirty state
- Verify: should maintain tree relationships and dirty state
- Insert and remove children
   - Expected: root.getChildCount() equals `1`
   - Expected: root.isDirty() is true
   - Expected: root.getChildCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should maintain tree relationships and dirty state")
step("Verify: should maintain tree relationships and dirty state")
# @req: REQ-TOOLS-Inde-001
step("Insert and remove children")
val root = Node.create()
val child = Node.create()
root.markLayoutSeen()
root.insertChild(child, 0)
expect(root.getChildCount()).to_equal(1)  # oracle: value fixed by the spec contract
expect(root.isDirty()).to_equal(true)
root.reset()
expect(root.getChildCount()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should store style setters and fast flags

- should store style setters and fast flags
- Verify: should store style setters and fast flags
- Set dimensions, flex, spacing, and position
   - Expected: node.getWidth().value equals `80`
   - Expected: node.getHeight().unit equals `UNIT_PERCENT`
   - Expected: node.getFlexGrow() equals `2`
   - Expected: node.getFlexShrink() equals `1`
   - Expected: node._hasAutoMargin is true
   - Expected: node._hasPadding is true
   - Expected: node._hasBorder is true
   - Expected: node._hasPosition is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should store style setters and fast flags")
step("Verify: should store style setters and fast flags")
# @req: REQ-TOOLS-Inde-001
step("Set dimensions, flex, spacing, and position")
val node = Node.create()
node.setWidth(80)
node.setHeightPercent(50)
node.setFlex(2)
node.setFlexDirection("row")
node.setMarginAuto(EDGE_LEFT)
node.setPadding(EDGE_TOP, 2)
node.setBorder(EDGE_BOTTOM, 1)
node.setPosition(EDGE_LEFT, 4)
expect(node.getWidth().value).to_equal(80)  # oracle: value fixed by the spec contract
expect(node.getHeight().unit).to_equal(UNIT_PERCENT)
expect(node.getFlexGrow()).to_equal(2)  # oracle: value fixed by the spec contract
expect(node.getFlexShrink()).to_equal(1)  # oracle: value fixed by the spec contract
expect(node._hasAutoMargin).to_equal(true)
expect(node._hasPadding).to_equal(true)
expect(node._hasBorder).to_equal(true)
expect(node._hasPosition).to_equal(true)
```

</details>

#### should calculate simple node layout

- should calculate simple node layout
- Verify: should calculate simple node layout
- Layout one node directly
   - Expected: root.getComputedWidth() equals `20`
   - Expected: root.getComputedHeight() equals `20`
   - Expected: root.isDirty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should calculate simple node layout")
step("Verify: should calculate simple node layout")
# @req: REQ-TOOLS-Inde-001
step("Layout one node directly")
val root = Node.create()
root.setWidth(20)
root.setHeight(20)
root.calculateLayout(20, 20, "ltr")
expect(root.getComputedWidth()).to_equal(20)  # oracle: value fixed by the spec contract
expect(root.getComputedHeight()).to_equal(20)  # oracle: value fixed by the spec contract
expect(root.isDirty()).to_equal(false)
```

</details>

#### should calculate row layout with gap and margins

- should calculate row layout with gap and margins
- Verify: should calculate row layout with gap and margins
- Resolve row helpers and spacing flags
   - Expected: root.getFlexDirection() equals `row`
   - Expected: resolveGap(root, "row") equals `2`
   - Expected: childMarginForAxis(a, "row") equals `0`
   - Expected: a._hasMargin is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should calculate row layout with gap and margins")
step("Verify: should calculate row layout with gap and margins")
# @req: REQ-TOOLS-Inde-001
step("Resolve row helpers and spacing flags")
val root = Node.create()
root.setFlexDirection("row")
root.setWidth(30)
root.setHeight(10)
root.setGap(0, 2)
val a = Node.create()
a.setWidth(5)
a.setHeight(3)
a.setMargin(EDGE_LEFT, 1)
expect(root.getFlexDirection()).to_equal("row")
expect(resolveGap(root, "row")).to_equal(2)  # oracle: value fixed by the spec contract
expect(childMarginForAxis(a, "row")).to_equal(0)  # oracle: value fixed by the spec contract
expect(a._hasMargin).to_equal(true)
```

</details>

#### should use measure functions and computed layout helpers

- should use measure functions and computed layout helpers
- Verify: should use measure functions and computed layout helpers
- Measure a leaf and read computed helpers
   - Expected: hasMeasureFuncInSubtree(child) is true
   - Expected: child.getComputedWidth() equals `7`
   - Expected: child.getComputedRight() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should use measure functions and computed layout helpers")
step("Verify: should use measure functions and computed layout helpers")
# @req: REQ-TOOLS-Inde-001
step("Measure a leaf and read computed helpers")
val child = Node.create()
child.setMeasureFunc(7, 4)
child.calculateLayout(7, 4, "ltr")
expect(hasMeasureFuncInSubtree(child)).to_equal(true)
expect(child.getComputedWidth()).to_equal(7)  # oracle: value fixed by the spec contract
expect(child.getComputedRight()).to_equal(0)  # oracle: value fixed by the spec contract
expect(child.getComputedLayout()).to_contain("7")
```

</details>

#### should reset, free, and zero hidden layouts

- should reset, free, and zero hidden layouts
- Verify: should reset, free, and zero hidden layouts
- Exercise lifecycle behavior
   - Expected: child.getComputedWidth() equals `0`
   - Expected: root.getChildCount() equals `0`
   - Expected: root.getDisplay() equals `flex`
   - Expected: child.getChildCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reset, free, and zero hidden layouts")
step("Verify: should reset, free, and zero hidden layouts")
# @req: REQ-TOOLS-Inde-001
step("Exercise lifecycle behavior")
val root = Node.create()
val child = Node.create()
child.setWidth(9)
child.setHeight(9)
child.setDisplay("none")
root.insertChild(child, 0)
root.calculateLayout(10, 10, "ltr")
expect(child.getComputedWidth()).to_equal(0)  # oracle: value fixed by the spec contract
root.reset()
expect(root.getChildCount()).to_equal(0)  # oracle: value fixed by the spec contract
expect(root.getDisplay()).to_equal("flex")
child.free()
expect(child.getChildCount()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should expose helper functions and source constant

- should expose helper functions and source constant
- Verify: should expose helper functions and source constant
- Pin source-backed helpers
   - Expected: boundAxis(20, pointValue(5), pointValue(10), 100) equals `10`
   - Expected: physicalEdge(EDGE_ALL) equals `EDGE_LEFT`
   - Expected: yogaSourceLinesModeled() equals `2578`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose helper functions and source constant")
step("Verify: should expose helper functions and source constant")
# @req: REQ-TOOLS-Inde-001
step("Pin source-backed helpers")
val node = Node.create()
node.setWidth(10)
node.setHeight(10)
layoutNode(node, 10, 10)
cacheWrite(node, 10, 10)
commitCacheOutputs(node)
expect(getYogaCounters()).to_contain("cache")
expect(boundAxis(20, pointValue(5), pointValue(10), 100)).to_equal(10)  # oracle: value fixed by the spec contract
expect(physicalEdge(EDGE_ALL)).to_equal(EDGE_LEFT)
expect(yogaSourceLinesModeled()).to_equal(2578)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Inde-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f1b835b63405c77e63f3ca2b4661a2621c424f3d42736f61d32f93454d8809de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f1b835b63405c77e63f3ca2b4661a2621c424f3d42736f61d32f93454d8809de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f1b835b63405c77e63f3ca2b4661a2621c424f3d42736f61d32f93454d8809de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve values, edges, and axis helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve values, edges, and axis helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create config and loader surfaces' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create config and loader surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should maintain tree relationships and dirty state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should maintain tree relationships and dirty state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should store style setters and fast flags' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:93:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should calculate simple node layout' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should calculate row layout with gap and margins' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
