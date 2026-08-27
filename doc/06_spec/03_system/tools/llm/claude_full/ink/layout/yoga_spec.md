# Claude Full Yoga Layout Node

> Purpose: should maintain child order and parent names

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Yoga Layout Node

Purpose: should maintain child order and parent names

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should maintain child order and parent names
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Yoga Layout Node

Checks the Yoga layout adapter tree, measurement, mapping, and lifecycle surface.

## Scenarios

### Claude full YogaLayoutNode

#### should maintain child order and parent names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should maintain child order and parent names
- Verify: should maintain child order and parent names
- Insert and remove Yoga layout children
   - Expected: parent.getChildCount() equals `2`
   - Expected: parent.children equals `["first", "second"]`
   - Expected: first.getParentName() equals `parent`
   - Expected: parent.children equals `["second"]`
   - Expected: first.getParentName() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should maintain child order and parent names")
step("Verify: should maintain child order and parent names")
# @req: REQ-TOOLS-Yoga-001
step("Insert and remove Yoga layout children")
val parent = createYogaLayoutNode("parent")
val first = createYogaLayoutNode("first")
val second = createYogaLayoutNode("second")
parent.insertChild(second, 0)
parent.insertChild(first, 0)
expect(parent.getChildCount()).to_equal(2)  # oracle: value fixed by the spec contract
expect(parent.children).to_equal(["first", "second"])
expect(first.getParentName()).to_equal("parent")
parent.removeChild(first)
expect(parent.children).to_equal(["second"])
expect(first.getParentName()).to_equal("")
```

</details>

#### should calculate layout from explicit measure results

- should calculate layout from explicit measure results
- Verify: should calculate layout from explicit measure results
- Mark dirty, measure, and calculate
   - Expected: node.dirty is false
   - Expected: node.measureMode equals `Exactly`
   - Expected: node.getComputedWidth() equals `24`
   - Expected: node.getComputedHeight() equals `7`
   - Expected: node.getStyle("direction") equals `ltr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should calculate layout from explicit measure results")
step("Verify: should calculate layout from explicit measure results")
# @req: REQ-TOOLS-Yoga-001
step("Mark dirty, measure, and calculate")
val node = createYogaLayoutNode("measured")
node.markDirty()
node.setMeasureResult(80, "exactly", 24, 7)
node.calculateLayout(100)
expect(node.dirty).to_equal(false)
expect(node.measureMode).to_equal("Exactly")
expect(node.getComputedWidth()).to_equal(24)  # oracle: value fixed by the spec contract
expect(node.getComputedHeight()).to_equal(7)  # oracle: value fixed by the spec contract
expect(node.getStyle("direction")).to_equal("ltr")
node.unsetMeasureFunc()
expect(node.measureResult).to_be_nil()
```

</details>

#### should record size setters and auto values

- should record size setters and auto values
- Verify: should record size setters and auto values
- Apply width, height, min, and max setters
   - Expected: node.getStyle("width") equals `10`
   - Expected: node.getStyle("widthPercent") equals `50`
   - Expected: node.getStyle("height") equals `auto`
   - Expected: node.getStyle("minWidth") equals `2`
   - Expected: node.getStyle("maxHeightPercent") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record size setters and auto values")
step("Verify: should record size setters and auto values")
# @req: REQ-TOOLS-Yoga-001
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

- should map flex, alignment, justification, display, and position type
- Verify: should map flex, alignment, justification, display, and position type
- Apply enum-like style setters
   - Expected: node.getStyle("flexDirection") equals `column-reverse`
   - Expected: node.getStyle("flexWrap") equals `wrap`
   - Expected: node.getStyle("alignItems") equals `center`
   - Expected: node.getStyle("alignSelf") equals `flex-end`
   - Expected: node.getStyle("justifyContent") equals `space-between`
   - Expected: node.getDisplay() equals `none`
   - Expected: node.getStyle("positionType") equals `absolute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should map flex, alignment, justification, display, and position type")
step("Verify: should map flex, alignment, justification, display, and position type")
# @req: REQ-TOOLS-Yoga-001
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

- should map edge, gutter, overflow, padding, border, margin, and position
- Verify: should map edge, gutter, overflow, padding, border, margin, and position
- Apply edge and gutter mapped setters
   - Expected: node.getStyle("position:left") equals `3`
   - Expected: node.getStyle("positionPercent:top") equals `25`
   - Expected: node.getStyle("overflow") equals `scroll`
   - Expected: node.getStyle("margin:all") equals `1`
   - Expected: node.getComputedPadding("horizontal") equals `2`
   - Expected: node.getComputedBorder("bottom") equals `4`
   - Expected: node.getStyle("gap:row") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should map edge, gutter, overflow, padding, border, margin, and position")
step("Verify: should map edge, gutter, overflow, padding, border, margin, and position")
# @req: REQ-TOOLS-Yoga-001
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
expect(node.getComputedPadding("horizontal")).to_equal(2)  # oracle: value fixed by the spec contract
expect(node.getComputedBorder("bottom")).to_equal(4)  # oracle: value fixed by the spec contract
expect(node.getStyle("gap:row")).to_equal("5")
```

</details>

#### should free nodes and expose source-backed mappings

- should free nodes and expose source-backed mappings
- Verify: should free nodes and expose source-backed mappings
- Run lifecycle methods and mapping helpers
   - Expected: node.freed is true
   - Expected: node.freedRecursive is true
   - Expected: mapEdge("bad") equals `all`
   - Expected: mapGutter("bad") equals `all`
   - Expected: mapMeasureMode("at-most") equals `AtMost`
   - Expected: mapOverflow("bad") equals `visible`
   - Expected: yogaLayoutNodeSourceLinesModeled() equals `308`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should free nodes and expose source-backed mappings")
step("Verify: should free nodes and expose source-backed mappings")
# @req: REQ-TOOLS-Yoga-001
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
expect(yogaLayoutNodeSourceLinesModeled()).to_equal(308)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Yoga-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1ace17d9d127e51bc680c86136e33f87b4e3d7d4df0c905dadf50efc2bb941f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ace17d9d127e51bc680c86136e33f87b4e3d7d4df0c905dadf50efc2bb941f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ace17d9d127e51bc680c86136e33f87b4e3d7d4df0c905dadf50efc2bb941f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/layout/yoga_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/layout/yoga_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/layout/yoga_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should maintain child order and parent names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should maintain child order and parent names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should calculate layout from explicit measure results' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should calculate layout from explicit measure results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record size setters and auto values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should record size setters and auto values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map flex, alignment, justification, display, and position type' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map edge, gutter, overflow, padding, border, margin, and position' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/layout/yoga_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should free nodes and expose source-backed mappings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
