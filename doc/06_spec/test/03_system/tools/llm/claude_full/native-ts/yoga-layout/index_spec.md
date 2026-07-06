# Claude Full Native Yoga Layout

> Checks Yoga layout parity for Node tree/style/layout behavior used by Ink.

<!-- sdn-diagram:id=index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

index_spec -> std
index_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Native Yoga Layout

Checks Yoga layout parity for Node tree/style/layout behavior used by Ink.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/native-ts/yoga-layout/index_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks Yoga layout parity for Node tree/style/layout behavior used by Ink.

## Scenarios

### Claude full native yoga layout

#### should resolve values, edges, and axis helpers

- Resolve point, percent, and edge precedence
   - Expected: resolveValue(pointValue(10), 100) equals `10`
   - Expected: resolveValue(percentValue(25), 200) equals `50`
- edges[EDGE HORIZONTAL] = pointValue
- edges[EDGE ALL] = pointValue
   - Expected: resolveEdge(edges, EDGE_LEFT, 100, false) equals `3`
   - Expected: resolveEdge(edges, EDGE_TOP, 100, false) equals `1`
   - Expected: isRow("row") is true
   - Expected: crossAxis("row") equals `column`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve point, percent, and edge precedence")
expect(resolveValue(pointValue(10), 100)).to_equal(10)
expect(resolveValue(percentValue(25), 200)).to_equal(50)
val edges = defaultEdges()
edges[EDGE_HORIZONTAL] = pointValue(3)
edges[EDGE_ALL] = pointValue(1)
expect(resolveEdge(edges, EDGE_LEFT, 100, false)).to_equal(3)
expect(resolveEdge(edges, EDGE_TOP, 100, false)).to_equal(1)
expect(isRow("row")).to_equal(true)
expect(crossAxis("row")).to_equal("column")
```

</details>

#### should create config and loader surfaces

- Configure Yoga
- config setPointScaleFactor
- config setErrata
- config setUseWebDefaults
   - Expected: config.pointScaleFactor equals `2`
   - Expected: config.getErrata() equals `classic`
   - Expected: loadYoga().hasNode is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Configure Yoga")
val config = createConfig()
config.setPointScaleFactor(2)
config.setErrata("classic")
config.setUseWebDefaults(true)
expect(config.pointScaleFactor).to_equal(2)
expect(config.getErrata()).to_equal("classic")
expect(loadYoga().hasNode).to_equal(true)
```

</details>

#### should maintain tree relationships and dirty state

- Insert and remove children
- root markLayoutSeen
- root insertChild
   - Expected: root.getChildCount() equals `1`
   - Expected: root.isDirty() is true
- root reset
   - Expected: root.getChildCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Insert and remove children")
val root = Node.create()
val child = Node.create()
root.markLayoutSeen()
root.insertChild(child, 0)
expect(root.getChildCount()).to_equal(1)
expect(root.isDirty()).to_equal(true)
root.reset()
expect(root.getChildCount()).to_equal(0)
```

</details>

#### should store style setters and fast flags

- Set dimensions, flex, spacing, and position
- node setWidth
- node setHeightPercent
- node setFlex
- node setFlexDirection
- node setMarginAuto
- node setPadding
- node setBorder
- node setPosition
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

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(node.getWidth().value).to_equal(80)
expect(node.getHeight().unit).to_equal(UNIT_PERCENT)
expect(node.getFlexGrow()).to_equal(2)
expect(node.getFlexShrink()).to_equal(1)
expect(node._hasAutoMargin).to_equal(true)
expect(node._hasPadding).to_equal(true)
expect(node._hasBorder).to_equal(true)
expect(node._hasPosition).to_equal(true)
```

</details>

#### should calculate simple node layout

- Layout one node directly
- root setWidth
- root setHeight
- root calculateLayout
   - Expected: root.getComputedWidth() equals `20`
   - Expected: root.getComputedHeight() equals `20`
   - Expected: root.isDirty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Layout one node directly")
val root = Node.create()
root.setWidth(20)
root.setHeight(20)
root.calculateLayout(20, 20, "ltr")
expect(root.getComputedWidth()).to_equal(20)
expect(root.getComputedHeight()).to_equal(20)
expect(root.isDirty()).to_equal(false)
```

</details>

#### should calculate row layout with gap and margins

- Resolve row helpers and spacing flags
- root setFlexDirection
- root setWidth
- root setHeight
- root setGap
- a setWidth
- a setHeight
- a setMargin
   - Expected: root.getFlexDirection() equals `row`
   - Expected: resolveGap(root, "row") equals `2`
   - Expected: childMarginForAxis(a, "row") equals `0`
   - Expected: a._hasMargin is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(resolveGap(root, "row")).to_equal(2)
expect(childMarginForAxis(a, "row")).to_equal(0)
expect(a._hasMargin).to_equal(true)
```

</details>

#### should use measure functions and computed layout helpers

- Measure a leaf and read computed helpers
- child setMeasureFunc
- child calculateLayout
   - Expected: hasMeasureFuncInSubtree(child) is true
   - Expected: child.getComputedWidth() equals `7`
   - Expected: child.getComputedRight() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure a leaf and read computed helpers")
val child = Node.create()
child.setMeasureFunc(7, 4)
child.calculateLayout(7, 4, "ltr")
expect(hasMeasureFuncInSubtree(child)).to_equal(true)
expect(child.getComputedWidth()).to_equal(7)
expect(child.getComputedRight()).to_equal(0)
expect(child.getComputedLayout()).to_contain("7")
```

</details>

#### should reset, free, and zero hidden layouts

- Exercise lifecycle behavior
- child setWidth
- child setHeight
- child setDisplay
- root insertChild
- root calculateLayout
   - Expected: child.getComputedWidth() equals `0`
- root reset
   - Expected: root.getChildCount() equals `0`
   - Expected: root.getDisplay() equals `flex`
- child free
   - Expected: child.getChildCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise lifecycle behavior")
val root = Node.create()
val child = Node.create()
child.setWidth(9)
child.setHeight(9)
child.setDisplay("none")
root.insertChild(child, 0)
root.calculateLayout(10, 10, "ltr")
expect(child.getComputedWidth()).to_equal(0)
root.reset()
expect(root.getChildCount()).to_equal(0)
expect(root.getDisplay()).to_equal("flex")
child.free()
expect(child.getChildCount()).to_equal(0)
```

</details>

#### should expose helper functions and source constant

- Pin source-backed helpers
- node setWidth
- node setHeight
- layoutNode
- cacheWrite
- commitCacheOutputs
   - Expected: boundAxis(20, pointValue(5), pointValue(10), 100) equals `10`
   - Expected: physicalEdge(EDGE_ALL) equals `EDGE_LEFT`
   - Expected: yogaSourceLinesModeled() equals `2578`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source-backed helpers")
val node = Node.create()
node.setWidth(10)
node.setHeight(10)
layoutNode(node, 10, 10)
cacheWrite(node, 10, 10)
commitCacheOutputs(node)
expect(getYogaCounters()).to_contain("cache")
expect(boundAxis(20, pointValue(5), pointValue(10), 100)).to_equal(10)
expect(physicalEdge(EDGE_ALL)).to_equal(EDGE_LEFT)
expect(yogaSourceLinesModeled()).to_equal(2578)
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
