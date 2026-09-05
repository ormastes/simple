# CSS Grid foundation

> This specification proves a bounded two-column CSS Grid slice through the canonical Simple Web rendering stack.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Grid foundation

This specification proves a bounded two-column CSS Grid slice through the canonical Simple Web rendering stack.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/feature/web_platform/css/grid_foundation_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification proves a bounded two-column CSS Grid slice through the
canonical Simple Web rendering stack.

The covered path is:

1. authored HTML and CSS;
2. computed Web style;
3. stable layout geometry;
4. canonical `DrawIrComposition`;
5. the existing Engine2D executor;
6. exact software-rendered pixel areas.

The primary scenario includes explicit column and row tracks, independent row
and column gaps, automatic placement in DOM order, a spanning item, and one
intrinsic implicit row.

A separate block control proves that ordinary vertical flow cannot satisfy the
Grid geometry by coincidence.

An abuse-boundary scenario proves that a declaration block over the renderer's
256-declaration quota is dropped wholesale.

That negative case prevents `display:grid` or any Grid longhand from leaking
through a rule that the ordinary declaration path rejected.

This is a foundation slice, not a claim of complete CSS Grid support.

It does not claim `fr`, `minmax()`, `repeat()`, named lines, named areas,
subgrid, dense placement, auto-fill, auto-fit, Grid alignment, or complete WPT
parity.

## Syntax

The container syntax exercised here is:

```css
display: grid;
grid-template-columns: 6px 10px;
grid-template-rows: 5px 7px;
column-gap: 2px;
row-gap: 2px;
```

Only positive integer pixel tracks are admitted by this bounded foundation.

Track values are normalized before they enter computed Draw IR style metadata.

The item placement syntax exercised here is:

```css
grid-column: 1 / span 2;
grid-row: 2;
```

and:

```css
grid-column: 2;
grid-row: 3;
```

Positive numeric lines are converted to zero-based internal track indices.

`start / span N` contributes a bounded positive column span.

A numeric row beyond the explicit row list creates an intrinsic implicit row
when it remains inside the per-layout occupancy capacity.

Invalid, nonnumeric, nonpositive, and out-of-capacity placement values fail
closed to bounded automatic placement.

## Examples

The retained example creates an 18-pixel-wide Grid.

Its first column is 6 pixels wide.

Its second column is 10 pixels wide.

The 2-pixel column gap accounts for the remaining width.

Items A and B are automatically placed in the first row.

Item C spans both columns in the second row.

Item D occupies column two in an implicit third row.

The resulting exact boxes are:

- Grid: `[0, 0, 18, 20]`;
- A: `[0, 0, 6, 5]`;
- B: `[8, 0, 10, 5]`;
- C: `[0, 7, 18, 7]`;
- D: `[8, 16, 10, 4]`.

The equivalent block control remains `[0, 0, 18, 21]`.

Its children stack at y coordinates 0, 5, 10, and 17.

## Semantic and Draw IR contract

The computed container display value must be exactly `grid`.

The normalized template styles must remain `6px 10px` and `5px 7px`.

The normalized item placements must remain visible on the corresponding Draw
IR commands.

Commands must remain in DOM order after their container command.

Every item command must retain the Grid container as `parent_id`.

The container clip must remain the 32 by 24 viewport clip.

No Grid-specific Draw IR command, cache, backend, or private paint path is
introduced by this foundation.

Web semantic/layout owners continue to emit the shared
`DrawIrComposition`.

Engine2D consumes that canonical composition unchanged.

## Pixel contract

The software Engine2D frame must report zero skipped commands.

The exact visible color areas are:

- A red: 30 pixels;
- B green: 50 pixels;
- C blue: 126 pixels;
- D magenta: 40 pixels.

The block control areas are 90, 90, 126, and 72 pixels respectively.

These unequal areas distinguish two-axis Grid placement from block stacking.

## Trust boundary

The renderer admits at most 256 declarations in one declaration block.

The negative scenario constructs exactly 257 declarations.

It combines five Grid declarations with 252 inert custom declarations.

The expected semantic display remains `block`.

All four Grid computed-style fields remain empty in Draw IR.

This is an all-or-nothing rejection contract, not graceful partial admission.

The ordinary non-Grid control continues through the existing declaration fast
path without a second Grid declaration-table build.

## Conformance provenance

The conformance basis is CSS Grid Layout Level 2:
`https://drafts.csswg.org/css-grid-2/`, retrieved 2026-07-29.

Corpus row
`simple-grid-foundation-explicit-tracks-span-implicit-row-v1` is a bounded
derived case retained in this file.

It is pinned to WPT revision
`6aab815f34c7c012a47202485e29dc8217e40877`.

The manifest is:
`test/fixtures/browser/conformance/pinned_manifest.env`, row `case_001`.

The retained source is:
`test/fixtures/browser/conformance/css_grid_foundation_explicit_tracks_span_implicit_row.html`.

Its SHA-256 is:
`2e53269d80cff2a3b2261f6ab4f698c2e4261523124bceff1736cf1fab141f3b`.

The manifest truthfully records `red-not-run`.

This documentation does not claim an upstream WPT import or executable PASS.

## Requirements

- Feature requirements:
  `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- Non-functional requirements:
  `doc/02_requirements/nfr/simple_web_browser_engine_production_hardening.md`
- Covered IDs: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
  REQ-WEB-BROWSER-019, and REQ-WEB-BROWSER-021.

## Plan

- Canonical system-test plan:
  `doc/03_plan/sys_test/html_css_spec_traceability.md`
- Parallel ownership and merge plan:
  `doc/03_plan/agent_tasks/html_css_spec_traceability.md`
- The canonical plan serializes this Grid foundation after the shared
  declaration/cascade lane.

## Design

- Production-hardening design:
  `doc/05_design/simple_web_browser_engine_production_hardening.md`
- Production-hardening architecture:
  `doc/04_architecture/simple_web_browser_engine_production_hardening.md`
- This specification preserves the existing Web semantic/layout to shared Draw
  IR to Engine2D ownership boundary.

## Research

- Local renderer research:
  `doc/01_research/local/simple_web_browser_engine_production_hardening.md`
- Domain standards research:
  `doc/01_research/domain/simple_web_browser_engine_production_hardening.md`

## Evidence status

The executable assertions are complete and independently reviewed.

The retained fixture hash and manifest row are statically verified.

Runtime execution remains unclaimed until a qualified pure-Simple target binary
runs this SSpec.

Generated manual completeness is a documentation gate only.

It cannot promote `red-not-run` corpus evidence to PASS.

## Scenarios

### REQ-WEB-BROWSER-003/004/019/021: CSS Grid foundation

#### should lower explicit tracks placement span and an implicit row

- Trace implemented CSS properties through canonical rendering
   - Artifact capture: after_step
- "<style>" +  grid common css
   - Artifact capture: after_step
- "<main id='grid'>" +  grid items
   - Artifact capture: after_step
   - Evidence: artifact verified by 13 expected checks
   - Expected: [a.x, a.y, a.width, a.height] equals `[0, 0, 6, 5]`
   - Expected: [b.x, b.y, b.width, b.height] equals `[8, 0, 10, 5]`
   - Expected: [c.x, c.y, c.width, c.height] equals `[0, 7, 18, 7]`
   - Expected: [d.x, d.y, d.width, d.height] equals `[8, 16, 10, 4]`
   - Expected: a.parent_id equals `grid`
   - Expected: b.parent_id equals `grid`
   - Expected: c.parent_id equals `grid`
   - Expected: d.parent_id equals `grid`
   - Expected: _grid_style(grid, "display") equals `grid`
   - Expected: _grid_style(c, "grid-column") equals `1 / span 2`
   - Expected: _grid_style(c, "grid-row") equals `2`
   - Expected: _grid_style(d, "grid-column") equals `2`
   - Expected: _grid_style(d, "grid-row") equals `3`
- backend shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: frame.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 104 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Trace implemented CSS properties through canonical rendering")
val html = (
    "<style>" + _grid_common_css() +
    "#grid{display:grid;width:18px;" +
    "grid-template-columns:6px 10px;" +
    "grid-template-rows:5px 7px;" +
    "column-gap:2px;row-gap:2px;background:#dbeafe}" +
    "#c{grid-column:1 / span 2;grid-row:2}" +
    "#d{grid-column:2;grid-row:3}</style>" +
    "<main id='grid'>" + _grid_items() + "</main>"
)

expect(simple_web_layout_debug_style_by_id(
    html, "grid", "display"
)).to_equal("grid")
expect(simple_web_layout_debug_layout_by_id(
    html, 32, 24, "c", "x"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    html, 32, 24, "c", "y"
)).to_equal("7")
expect(simple_web_layout_debug_layout_by_id(
    html, 32, 24, "c", "w"
)).to_equal("18")
expect(simple_web_layout_debug_layout_by_id(
    html, 32, 24, "d", "x"
)).to_equal("8")
expect(simple_web_layout_debug_layout_by_id(
    html, 32, 24, "d", "y"
)).to_equal("16")

val composition = simple_web_layout_render_html_draw_ir(
    html, 32, 24
)
expect(composition.batches.len()).to_be_greater_than(0)
val commands: [DrawIrCommand] = if composition.batches.len() > 0:
    composition.batches[0].commands
else:
    []
val grid_index = _grid_command_index(commands, "grid")
val a_index = _grid_command_index(commands, "a")
val b_index = _grid_command_index(commands, "b")
val c_index = _grid_command_index(commands, "c")
val d_index = _grid_command_index(commands, "d")
expect(grid_index).to_be_greater_than(-1)
expect(a_index).to_be_greater_than(grid_index)
expect(b_index).to_be_greater_than(a_index)
expect(c_index).to_be_greater_than(b_index)
expect(d_index).to_be_greater_than(c_index)

if (
    grid_index >= 0 and a_index >= 0 and b_index >= 0 and
    c_index >= 0 and d_index >= 0
):
    val grid = commands[grid_index]
    val a = commands[a_index]
    val b = commands[b_index]
    val c = commands[c_index]
    val d = commands[d_index]
    expect([grid.x, grid.y, grid.width, grid.height]).to_equal(
        [0, 0, 18, 20]
    )
    expect([a.x, a.y, a.width, a.height]).to_equal([0, 0, 6, 5])
    expect([b.x, b.y, b.width, b.height]).to_equal([8, 0, 10, 5])
    expect([c.x, c.y, c.width, c.height]).to_equal([0, 7, 18, 7])
    expect([d.x, d.y, d.width, d.height]).to_equal([8, 16, 10, 4])
    expect(a.parent_id).to_equal("grid")
    expect(b.parent_id).to_equal("grid")
    expect(c.parent_id).to_equal("grid")
    expect(d.parent_id).to_equal("grid")
    expect([
        grid.clip_rect.x, grid.clip_rect.y,
        grid.clip_rect.width, grid.clip_rect.height
    ]).to_equal([0, 0, 32, 24])
    expect(_grid_style(grid, "display")).to_equal("grid")
    expect(_grid_style(
        grid, "grid-template-columns"
    )).to_equal("6px 10px")
    expect(_grid_style(
        grid, "grid-template-rows"
    )).to_equal("5px 7px")
    expect(_grid_style(c, "grid-column")).to_equal("1 / span 2")
    expect(_grid_style(c, "grid-row")).to_equal("2")
    expect(_grid_style(d, "grid-column")).to_equal("2")
    expect(_grid_style(d, "grid-row")).to_equal("3")

val backend = Engine2dCompositorBackend.create_named(
    32, 24, "software"
)
val frame = backend.render_draw_ir_composition(composition, [])
backend.shutdown()
expect(frame.skipped_command_count).to_equal(0)
expect(_grid_color_count(
    frame.pixels, 0xFFEF4444u32
)).to_equal(30)
expect(_grid_color_count(
    frame.pixels, 0xFF22C55Eu32
)).to_equal(50)
expect(_grid_color_count(
    frame.pixels, 0xFF2563EBu32
)).to_equal(126)
expect(_grid_color_count(
    frame.pixels, 0xFFD946EFu32
)).to_equal(40)
```

</details>

<details>
<summary>Advanced: should drop an over-quota Grid rule without partial mutation</summary>

#### should drop an over-quota Grid rule without partial mutation

- Trace implemented CSS properties through canonical rendering
- "<style>#quota{" +  grid over quota declarations
   - Expected: _grid_style(quota, "display") equals `block`
   - Expected: _grid_style(quota, "grid-column") equals ``
   - Expected: _grid_style(quota, "grid-row") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Trace implemented CSS properties through canonical rendering")
val html = (
    "<style>#quota{" + _grid_over_quota_declarations() +
    "}</style><main id='quota'><div id='child'></div></main>"
)

expect(simple_web_layout_debug_style_by_id(
    html, "quota", "display"
)).to_equal("block")
val composition = simple_web_layout_render_html_draw_ir(
    html, 32, 24
)
expect(composition.batches.len()).to_be_greater_than(0)
val commands: [DrawIrCommand] = if composition.batches.len() > 0:
    composition.batches[0].commands
else:
    []
val quota_index = _grid_command_index(commands, "quota")
expect(quota_index).to_be_greater_than(-1)
if quota_index >= 0:
    val quota = commands[quota_index]
    expect(_grid_style(quota, "display")).to_equal("block")
    expect(_grid_style(
        quota, "grid-template-columns"
    )).to_equal("")
    expect(_grid_style(
        quota, "grid-template-rows"
    )).to_equal("")
    expect(_grid_style(quota, "grid-column")).to_equal("")
    expect(_grid_style(quota, "grid-row")).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: should keep the equivalent block control in vertical flow</summary>

#### should keep the equivalent block control in vertical flow

- Trace implemented CSS properties through canonical rendering
- "<style>" +  grid common css
- "</style><main id='control'>" +  grid items
   - Expected: [a.x, a.y, a.width, a.height] equals `[0, 0, 18, 5]`
   - Expected: [b.x, b.y, b.width, b.height] equals `[0, 5, 18, 5]`
   - Expected: [c.x, c.y, c.width, c.height] equals `[0, 10, 18, 7]`
   - Expected: [d.x, d.y, d.width, d.height] equals `[0, 17, 18, 4]`
   - Expected: a.parent_id equals `control`
   - Expected: b.parent_id equals `control`
   - Expected: c.parent_id equals `control`
   - Expected: d.parent_id equals `control`
   - Expected: _grid_style(control, "display") equals `block`
- backend shutdown
   - Expected: frame.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Trace implemented CSS properties through canonical rendering")
val html = (
    "<style>" + _grid_common_css() +
    "#control{display:block;width:18px;background:#dbeafe}" +
    "</style><main id='control'>" + _grid_items() + "</main>"
)

expect(simple_web_layout_debug_style_by_id(
    html, "control", "display"
)).to_equal("block")
val composition = simple_web_layout_render_html_draw_ir(
    html, 32, 24
)
expect(composition.batches.len()).to_be_greater_than(0)
val commands: [DrawIrCommand] = if composition.batches.len() > 0:
    composition.batches[0].commands
else:
    []
val control_index = _grid_command_index(commands, "control")
val a_index = _grid_command_index(commands, "a")
val b_index = _grid_command_index(commands, "b")
val c_index = _grid_command_index(commands, "c")
val d_index = _grid_command_index(commands, "d")
expect(control_index).to_be_greater_than(-1)
expect(a_index).to_be_greater_than(control_index)
expect(b_index).to_be_greater_than(a_index)
expect(c_index).to_be_greater_than(b_index)
expect(d_index).to_be_greater_than(c_index)

if (
    control_index >= 0 and a_index >= 0 and b_index >= 0 and
    c_index >= 0 and d_index >= 0
):
    val control = commands[control_index]
    val a = commands[a_index]
    val b = commands[b_index]
    val c = commands[c_index]
    val d = commands[d_index]
    expect([
        control.x, control.y, control.width, control.height
    ]).to_equal([0, 0, 18, 21])
    expect([a.x, a.y, a.width, a.height]).to_equal([0, 0, 18, 5])
    expect([b.x, b.y, b.width, b.height]).to_equal([0, 5, 18, 5])
    expect([c.x, c.y, c.width, c.height]).to_equal([0, 10, 18, 7])
    expect([d.x, d.y, d.width, d.height]).to_equal([0, 17, 18, 4])
    expect(a.parent_id).to_equal("control")
    expect(b.parent_id).to_equal("control")
    expect(c.parent_id).to_equal("control")
    expect(d.parent_id).to_equal("control")
    expect(_grid_style(control, "display")).to_equal("block")

val backend = Engine2dCompositorBackend.create_named(
    32, 24, "software"
)
val frame = backend.render_draw_ir_composition(composition, [])
backend.shutdown()
expect(frame.skipped_command_count).to_equal(0)
expect(_grid_color_count(
    frame.pixels, 0xFFEF4444u32
)).to_equal(90)
expect(_grid_color_count(
    frame.pixels, 0xFF22C55Eu32
)).to_equal(90)
expect(_grid_color_count(
    frame.pixels, 0xFF2563EBu32
)).to_equal(126)
expect(_grid_color_count(
    frame.pixels, 0xFFD946EFu32
)).to_equal(72)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/html_css_spec_traceability.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>
