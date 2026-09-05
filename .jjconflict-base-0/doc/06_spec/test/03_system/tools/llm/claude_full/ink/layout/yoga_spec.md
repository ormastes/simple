# Claude Full Yoga Layout Node

> Checks the Yoga layout adapter tree, measurement, mapping, and lifecycle surface.

<!-- sdn-diagram:id=yoga_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=yoga_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

yoga_spec -> std
yoga_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=yoga_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Yoga Layout Node

Checks the Yoga layout adapter tree, measurement, mapping, and lifecycle surface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the Yoga layout adapter tree, measurement, mapping, and lifecycle surface.

## Scenarios

### Claude full YogaLayoutNode

#### should maintain child order and parent names

- Insert and remove Yoga layout children
- parent insertChild
- parent insertChild
   - Expected: parent.getChildCount() equals `2`
   - Expected: parent.children equals `["first", "second"]`
   - Expected: first.getParentName() equals `parent`
- parent removeChild
   - Expected: parent.children equals `["second"]`
   - Expected: first.getParentName() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Insert and remove Yoga layout children")
val parent = createYogaLayoutNode("parent")
val first = createYogaLayoutNode("first")
val second = createYogaLayoutNode("second")
parent.insertChild(second, 0)
parent.insertChild(first, 0)
expect(parent.getChildCount()).to_equal(2)
expect(parent.children).to_equal(["first", "second"])
expect(first.getParentName()).to_equal("parent")
parent.removeChild(first)
expect(parent.children).to_equal(["second"])
expect(first.getParentName()).to_equal("")
```

</details>

#### should calculate layout from explicit measure results

- Mark dirty, measure, and calculate
- node markDirty
- node setMeasureResult
- node calculateLayout
   - Expected: node.dirty is false
   - Expected: node.measureMode equals `Exactly`
   - Expected: node.getComputedWidth() equals `24`
   - Expected: node.getComputedHeight() equals `7`
   - Expected: node.getStyle("direction") equals `ltr`
- node unsetMeasureFunc


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mark dirty, measure, and calculate")
val node = createYogaLayoutNode("measured")
node.markDirty()
node.setMeasureResult(80, "exactly", 24, 7)
node.calculateLayout(100)
expect(node.dirty).to_equal(false)
expect(node.measureMode).to_equal("Exactly")
expect(node.getComputedWidth()).to_equal(24)
expect(node.getComputedHeight()).to_equal(7)
expect(node.getStyle("direction")).to_equal("ltr")
node.unsetMeasureFunc()
expect(node.measureResult).to_be_nil()
```

</details>

#### should record size setters and auto values

- Apply width, height, min, and max setters
- node setWidth
- node setWidthPercent
- node setHeight
- node setHeightAuto
- node setMinWidth
- node setMaxHeightPercent
   - Expected: node.getStyle("width") equals `10`
   - Expected: node.getStyle("widthPercent") equals `50`
   - Expected: node.getStyle("height") equals `auto`
   - Expected: node.getStyle("minWidth") equals `2`
   - Expected: node.getStyle("maxHeightPercent") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply width, height, min, and max setters")
val node = createYogaLayoutNode("box")
node.setWidth(10)
node.setWidthPercent(50)
node.setHeight(4)
node.setHeightAuto()
node.setMinWidth(2)
node.setMaxHeightPercent(90)
expect(node.getStyle("width")).to_equal("10")
expect(node.getStyle("widthPercent")).to_equal("50")
expect(node.getStyle("height")).to_equal("auto")
expect(node.getStyle("minWidth")).to_equal("2")
expect(node.getStyle("maxHeightPercent")).to_equal("90")
```

</details>

#### should map flex, alignment, justification, display, and position type

- Apply enum-like style setters
- node setFlexDirection
- node setFlexWrap
- node setAlignItems
- node setAlignSelf
- node setJustifyContent
- node setDisplay
- node setPositionType
   - Expected: node.getStyle("flexDirection") equals `column-reverse`
   - Expected: node.getStyle("flexWrap") equals `wrap`
   - Expected: node.getStyle("alignItems") equals `center`
   - Expected: node.getStyle("alignSelf") equals `flex-end`
   - Expected: node.getStyle("justifyContent") equals `space-between`
   - Expected: node.getDisplay() equals `none`
   - Expected: node.getStyle("positionType") equals `absolute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply enum-like style setters")
val node = createYogaLayoutNode("style")
node.setFlexDirection("column-reverse")
node.setFlexWrap("wrap")
node.setAlignItems("center")
node.setAlignSelf("flex-end")
node.setJustifyContent("space-between")
node.setDisplay("none")
node.setPositionType("absolute")
expect(node.getStyle("flexDirection")).to_equal("column-reverse")
expect(node.getStyle("flexWrap")).to_equal("wrap")
expect(node.getStyle("alignItems")).to_equal("center")
expect(node.getStyle("alignSelf")).to_equal("flex-end")
expect(node.getStyle("justifyContent")).to_equal("space-between")
expect(node.getDisplay()).to_equal("none")
expect(node.getStyle("positionType")).to_equal("absolute")
```

</details>

#### should map edge, gutter, overflow, padding, border, margin, and position

- Apply edge and gutter mapped setters
- node setPosition
- node setPositionPercent
- node setOverflow
- node setMargin
- node setPadding
- node setBorder
- node setGap
   - Expected: node.getStyle("position:left") equals `3`
   - Expected: node.getStyle("positionPercent:top") equals `25`
   - Expected: node.getStyle("overflow") equals `scroll`
   - Expected: node.getStyle("margin:all") equals `1`
   - Expected: node.getComputedPadding("horizontal") equals `2`
   - Expected: node.getComputedBorder("bottom") equals `4`
   - Expected: node.getStyle("gap:row") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply edge and gutter mapped setters")
val node = createYogaLayoutNode("edges")
node.setPosition("left", 3)
node.setPositionPercent("top", 25)
node.setOverflow("scroll")
node.setMargin("all", 1)
node.setPadding("horizontal", 2)
node.setBorder("bottom", 4)
node.setGap("row", 5)
expect(node.getStyle("position:left")).to_equal("3")
expect(node.getStyle("positionPercent:top")).to_equal("25")
expect(node.getStyle("overflow")).to_equal("scroll")
expect(node.getStyle("margin:all")).to_equal("1")
expect(node.getComputedPadding("horizontal")).to_equal(2)
expect(node.getComputedBorder("bottom")).to_equal(4)
expect(node.getStyle("gap:row")).to_equal("5")
```

</details>

#### should free nodes and expose source-backed mappings

- Run lifecycle methods and mapping helpers
- node free
   - Expected: node.freed is true
- node freeRecursive
   - Expected: node.freedRecursive is true
   - Expected: mapEdge("bad") equals `all`
   - Expected: mapGutter("bad") equals `all`
   - Expected: mapMeasureMode("at-most") equals `AtMost`
   - Expected: mapOverflow("bad") equals `visible`
   - Expected: yogaLayoutNodeSourceLinesModeled() equals `308`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run lifecycle methods and mapping helpers")
val node = createYogaLayoutNode("life")
node.free()
expect(node.freed).to_equal(true)
node.freeRecursive()
expect(node.freedRecursive).to_equal(true)
expect(mapEdge("bad")).to_equal("all")
expect(mapGutter("bad")).to_equal("all")
expect(mapMeasureMode("at-most")).to_equal("AtMost")
expect(mapOverflow("bad")).to_equal("visible")
expect(yogaLayoutNodeSourceLinesModeled()).to_equal(308)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
