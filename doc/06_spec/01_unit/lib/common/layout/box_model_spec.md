# Box Model Specification

> `common.layout.box_model` is the shared CSS spacing record used by the ui.browser layout backend. This spec pins its arithmetic, and — because the tree has repeatedly grown divergent copies of the same box record — pins that the blink render lane's `BoxGeometry` still means the same thing by the same twelve field names. A copy that drifts turns this spec red instead of rotting silently.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Box Model Specification

`common.layout.box_model` is the shared CSS spacing record used by the ui.browser layout backend. This spec pins its arithmetic, and — because the tree has repeatedly grown divergent copies of the same box record — pins that the blink render lane's `BoxGeometry` still means the same thing by the same twelve field names. A copy that drifts turns this spec red instead of rotting silently.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Common / Layout |
| Status | Active |
| Source | `test/01_unit/lib/common/layout/box_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`common.layout.box_model` is the shared CSS spacing record used by the
ui.browser layout backend. This spec pins its arithmetic, and — because the
tree has repeatedly grown divergent copies of the same box record — pins that
the blink render lane's `BoxGeometry` still means the same thing by the same
twelve field names. A copy that drifts turns this spec red instead of rotting
silently.

## Scenarios

### Box-model spacing

#### reports zero consumed space when every edge is zero

- reports zero consumed space when every edge is zero
- Build a box model with all twelve edges at zero
- Verify it consumes no horizontal or vertical space


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports zero consumed space when every edge is zero")
step("Build a box model with all twelve edges at zero")
val m = BoxModel.zero()

step("Verify it consumes no horizontal or vertical space")
assert_true(approx_eq(m.horizontal_space(), 0.0))
assert_true(approx_eq(m.vertical_space(), 0.0))
```

</details>

#### sums both sides of margin, padding and border into consumed space

- sums both sides of margin, padding and border into consumed space
- Build a box model with 10px margin and 4px padding on every side
- Verify each axis consumes both sides: 2*(10+4) = 28


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sums both sides of margin, padding and border into consumed space")
step("Build a box model with 10px margin and 4px padding on every side")
val m = BoxModel.uniform(10.0, 4.0)

step("Verify each axis consumes both sides: 2*(10+4) = 28")
assert_true(approx_eq(m.horizontal_space(), 28.0))
assert_true(approx_eq(m.vertical_space(), 28.0))
```

</details>

#### places a uniform margin on all four sides and leaves borders at zero

- places a uniform margin on all four sides and leaves borders at zero
- Build a box model with 3px margin and 7px padding
- Verify each margin edge is 3 and each padding edge is 7
- Verify uniform() leaves every border edge at zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("places a uniform margin on all four sides and leaves borders at zero")
step("Build a box model with 3px margin and 7px padding")
val m = BoxModel.uniform(3.0, 7.0)

step("Verify each margin edge is 3 and each padding edge is 7")
assert_true(approx_eq(m.margin_top, 3.0))
assert_true(approx_eq(m.margin_right, 3.0))
assert_true(approx_eq(m.margin_bottom, 3.0))
assert_true(approx_eq(m.margin_left, 3.0))
assert_true(approx_eq(m.padding_top, 7.0))
assert_true(approx_eq(m.padding_right, 7.0))
assert_true(approx_eq(m.padding_bottom, 7.0))
assert_true(approx_eq(m.padding_left, 7.0))

step("Verify uniform() leaves every border edge at zero")
assert_true(approx_eq(m.border_top, 0.0))
assert_true(approx_eq(m.border_right, 0.0))
assert_true(approx_eq(m.border_bottom, 0.0))
assert_true(approx_eq(m.border_left, 0.0))
```

</details>

### Layout box hit testing

#### contains a point in its interior

- contains a point in its interior
- Create a 100x50 box at the origin
- Verify an interior point is inside


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains a point in its interior")
step("Create a 100x50 box at the origin")
var b = BlockLayoutBox.create(1, BoxKind.Block)
b.width = 100.0
b.height = 50.0

step("Verify an interior point is inside")
assert_true(b.contains(50.0, 25.0))
```

</details>

#### contains its own top-left corner but not its bottom-right corner

- contains its own top-left corner but not its bottom-right corner
- Create a 100x50 box at the origin
- Verify the top-left corner is inside (half-open rectangle)
- Verify the bottom-right corner is outside


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains its own top-left corner but not its bottom-right corner")
step("Create a 100x50 box at the origin")
var b = BlockLayoutBox.create(1, BoxKind.Block)
b.width = 100.0
b.height = 50.0

step("Verify the top-left corner is inside (half-open rectangle)")
assert_true(b.contains(0.0, 0.0))

step("Verify the bottom-right corner is outside")
assert_false(b.contains(100.0, 50.0))
```

</details>

#### reports its right and bottom edges from origin plus extent

- reports its right and bottom edges from origin plus extent
- Create a 100x50 box offset to (10, 20)
- Verify right is 110 and bottom is 70


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports its right and bottom edges from origin plus extent")
step("Create a 100x50 box offset to (10, 20)")
var b = BlockLayoutBox.create(1, BoxKind.Block)
b.x = 10.0
b.y = 20.0
b.width = 100.0
b.height = 50.0

step("Verify right is 110 and bottom is 70")
assert_true(approx_eq(b.right(), 110.0))
assert_true(approx_eq(b.bottom(), 70.0))
```

</details>

### Spacing parity across the layout lanes

#### exposes the shared BoxModel itself, edge-for-edge, as its spacing field

- exposes the shared BoxModel itself, edge-for-edge, as its spacing field
- Build the shared record directly and via the blink constructor
- Verify all four margin edges match between the two lanes
- Verify all four padding edges match between the two lanes
- Verify all four border edges match between the two lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes the shared BoxModel itself, edge-for-edge, as its spacing field")
step("Build the shared record directly and via the blink constructor")
val m = BoxModel.uniform(6.0, 2.0)
val g = box_geometry_new(100.0, 40.0, 6.0, 2.0, 0.0)

step("Verify all four margin edges match between the two lanes")
assert_true(approx_eq(m.margin_top, g.spacing.margin_top))
assert_true(approx_eq(m.margin_right, g.spacing.margin_right))
assert_true(approx_eq(m.margin_bottom, g.spacing.margin_bottom))
assert_true(approx_eq(m.margin_left, g.spacing.margin_left))

step("Verify all four padding edges match between the two lanes")
assert_true(approx_eq(m.padding_top, g.spacing.padding_top))
assert_true(approx_eq(m.padding_right, g.spacing.padding_right))
assert_true(approx_eq(m.padding_bottom, g.spacing.padding_bottom))
assert_true(approx_eq(m.padding_left, g.spacing.padding_left))

step("Verify all four border edges match between the two lanes")
assert_true(approx_eq(m.border_top, g.spacing.border_top))
assert_true(approx_eq(m.border_right, g.spacing.border_right))
assert_true(approx_eq(m.border_bottom, g.spacing.border_bottom))
assert_true(approx_eq(m.border_left, g.spacing.border_left))
```

</details>

#### lets the blink lane call the shared spacing helpers directly

- lets the blink lane call the shared spacing helpers directly
- Build both spacing records with 5px margin, 3px padding, 1px border
- Compute the blink lane's horizontal space by hand from its own edges
- Verify the shared helper reports the same 18px total
- Verify the blink record answers the shared helper identically
- Compute the blink lane's vertical space by hand and verify parity


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets the blink lane call the shared spacing helpers directly")
step("Build both spacing records with 5px margin, 3px padding, 1px border")
val m = BoxModel(
    margin_top: 5.0, margin_right: 5.0, margin_bottom: 5.0, margin_left: 5.0,
    padding_top: 3.0, padding_right: 3.0, padding_bottom: 3.0, padding_left: 3.0,
    border_top: 1.0, border_right: 1.0, border_bottom: 1.0, border_left: 1.0
)
val g = box_geometry_new(100.0, 40.0, 5.0, 3.0, 1.0)

step("Compute the blink lane's horizontal space by hand from its own edges")
val g_horizontal = g.spacing.margin_left + g.spacing.padding_left +
    g.spacing.border_left + g.spacing.border_right +
    g.spacing.padding_right + g.spacing.margin_right

step("Verify the shared helper reports the same 18px total")
assert_true(approx_eq(m.horizontal_space(), 18.0))
assert_true(approx_eq(m.horizontal_space(), g_horizontal))

step("Verify the blink record answers the shared helper identically")
assert_true(approx_eq(g.spacing.horizontal_space(), 18.0))
assert_true(approx_eq(g.spacing.vertical_space(), m.vertical_space()))

step("Compute the blink lane's vertical space by hand and verify parity")
val g_vertical = g.spacing.margin_top + g.spacing.padding_top +
    g.spacing.border_top + g.spacing.border_bottom +
    g.spacing.padding_bottom + g.spacing.margin_bottom
assert_true(approx_eq(m.vertical_space(), g_vertical))
```

</details>

#### agrees that a zeroed record consumes no space in either lane

- agrees that a zeroed record consumes no space in either lane
- Build a zeroed record in each lane
- Verify every blink edge is zero, matching BoxModel.zero()
- Verify the shared helper agrees no space is consumed


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("agrees that a zeroed record consumes no space in either lane")
step("Build a zeroed record in each lane")
val m = BoxModel.zero()
val g = box_geometry_zero()

step("Verify every blink edge is zero, matching BoxModel.zero()")
assert_true(approx_eq(m.margin_top, g.spacing.margin_top))
assert_true(approx_eq(m.padding_left, g.spacing.padding_left))
assert_true(approx_eq(m.border_bottom, g.spacing.border_bottom))

step("Verify the shared helper agrees no space is consumed")
assert_true(approx_eq(m.horizontal_space(), 0.0))
assert_true(approx_eq(m.vertical_space(), 0.0))
assert_true(approx_eq(g.spacing.horizontal_space(), 0.0))
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

- `REQ-SSPEC-UNIT`
- `REQ-LAYOUT-BOXMODEL-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b5595531ad4d3ad78b51f0c0496d825eec79cb105c27aa684217b16220f550e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b5595531ad4d3ad78b51f0c0496d825eec79cb105c27aa684217b16220f550e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b5595531ad4d3ad78b51f0c0496d825eec79cb105c27aa684217b16220f550e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/layout/box_model_spec.spl
mirror: doc/06_spec/01_unit/lib/common/layout/box_model_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/layout/box_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/layout/box_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/layout/box_model_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/layout/box_model_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports zero consumed space when every edge is zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/layout/box_model_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums both sides of margin, padding and border into consumed space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/layout/box_model_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places a uniform margin on all four sides and leaves borders at zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
