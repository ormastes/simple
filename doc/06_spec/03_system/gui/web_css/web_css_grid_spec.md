# Web CSS Grid Layout System Test

> A reader wants to know whether the headless web/HTML-CSS renderer computes

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web CSS Grid Layout System Test

A reader wants to know whether the headless web/HTML-CSS renderer computes

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.3) |
| Source | `test/03_system/gui/web_css/web_css_grid_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A reader wants to know whether the headless web/HTML-CSS renderer computes
CSS Grid layout correctly: fixed pixel track sizing, `fr` (flexible) track
sizing, `grid-column` spans across tracks, gap separating tracks on both
axes, named-area placement via `grid-template-areas`/`grid-area`, and
column-first auto-placement via `grid-auto-flow: column`.

## Scope and Preconditions

Runs entirely in-process, headless, no display server:
`simple_web_layout_render_html_draw_ir(html, width, height)` produces a
`common.ui.draw_ir.DrawIrComposition`. Every assertion reads computed box
geometry straight off `DrawIrCommand` (`x`/`y`/`width`/`height` = border box)
— never a "didn't crash" check. Every geometry assertion first confirms the
element's Draw IR command was actually emitted (`_draw_ir_index_by_id >= 0`);
the id lookup helper fails open to `commands[0]` on a miss, so skipping this
check would let a missing command masquerade as `x == 0` and pass vacuously.

## Primary Workflow

Render small fixed HTML/CSS fixtures at a fixed viewport, look up the command
for a named element by `component_id`, and assert exact computed pixel
geometry.

## Resolved Renderer Gaps (verified by direct probe against the real
renderer, not assumed from the CSS spec)

`normalized_grid_track_list` (`simple_web_html_layout_renderer_declarations.spl`)
now parses `<n>fr` tokens alongside `<n>px` tokens, and `grid_track_sizes`
(`simple_web_html_layout_renderer_layout.spl`) resolves them at layout time:
fixed `px` tracks are subtracted from the container's content-box width,
and the remaining free space is distributed across `fr` tracks proportional
to their flex factor (CSS Grid SS11.5, simplified — no `minmax()`, no
min-content clamping, and row-axis `fr` resolves to 0px since auto row
height isn't generally known ahead of layout). See
`doc/08_tracking/bug/browser_engine_grid_fr_track_unit_unsupported_2026-08-07.md`
for the resolved bug record and noted simplifications.

`grid-template-areas`/`grid-area` and `grid-auto-flow: column` are now
implemented: `normalized_grid_template_areas`/`normalized_grid_area`/
`normalized_grid_auto_flow` (`simple_web_html_layout_renderer_declarations.spl`)
parse the declarations, and `grid_template_area_rects` plus a flow-mode
branch in the auto-placement candidate walk
(`simple_web_html_layout_renderer_layout.spl`) resolve named-area placement
and column-first auto-placement respectively — simplified: only rectangular
areas (CSS Grid SS7.1), no `.` dot-cell handling beyond treating it as an
empty cell, no implicit-track creation beyond what the template implies,
and no `grid-auto-flow: dense`. See
`doc/08_tracking/bug/browser_engine_grid_template_areas_missing_2026-08.md`
for the resolved bug record and noted simplifications.

## Evidence and Provenance

DrawIR-tree oracle per plan §3.6; source:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`.

## Scenarios

### Web CSS grid layout

#### fixed pixel tracks position cells exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Grid layout geometry" (expected show, folded, detail, or skip)


- fixed pixel tracks position cells exactly
- Render a grid container with two fixed pixel column tracks
- Assert both cells' Draw IR commands were actually emitted
- Assert cell a occupies the first 20px track and cell b the next 30px track
   - Expected: a.x equals `grid.x`
   - Expected: a.width equals `20`
   - Expected: b.x equals `a.x + 20`
   - Expected: b.width equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixed pixel tracks position cells exactly")
step("Render a grid container with two fixed pixel column tracks")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff;}" +
    "#grid{display:grid;grid-template-columns:20px 30px;" +
    "width:60px;height:10px;background-color:#e5e7eb;}" +
    "#a{background-color:#ef4444;}" +
    "#b{background-color:#22c55e;}" +
    "</style></head><body><div id='grid'>" +
    "<div id='a'></div><div id='b'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands

step("Assert both cells' Draw IR commands were actually emitted")
assert_true(_draw_ir_index_by_id(commands, "grid") >= 0)
assert_true(_draw_ir_index_by_id(commands, "a") >= 0)
assert_true(_draw_ir_index_by_id(commands, "b") >= 0)

val grid = _draw_ir_command_by_id(commands, "grid")
val a = _draw_ir_command_by_id(commands, "a")
val b = _draw_ir_command_by_id(commands, "b")

step("Assert cell a occupies the first 20px track and cell b the next 30px track")
expect(a.x).to_equal(grid.x)
expect(a.width).to_equal(20)
expect(b.x).to_equal(a.x + 20)
expect(b.width).to_equal(30)
```

</details>

#### grid-template-columns: fr tracks split remaining space proportionally

- grid-template-columns: fr tracks split remaining space proportionally
- Render a grid container with two fr column tracks over a 60px container
- Assert both cells' Draw IR commands were actually emitted
- Assert the 60px remaining space splits 1:2 (20px/40px) per CSS Grid
   - Expected: a.width equals `20`
   - Expected: b.x equals `20`
   - Expected: b.width equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("grid-template-columns: fr tracks split remaining space proportionally")
step("Render a grid container with two fr column tracks over a 60px container")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff;}" +
    "#grid{display:grid;grid-template-columns:1fr 2fr;" +
    "width:60px;height:10px;background-color:#e5e7eb;}" +
    "#a{background-color:#ef4444;height:10px;}" +
    "#b{background-color:#22c55e;height:10px;}" +
    "</style></head><body><div id='grid'>" +
    "<div id='a'></div><div id='b'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands

step("Assert both cells' Draw IR commands were actually emitted")
assert_true(_draw_ir_index_by_id(commands, "a") >= 0)
assert_true(_draw_ir_index_by_id(commands, "b") >= 0)

val a = _draw_ir_command_by_id(commands, "a")
val b = _draw_ir_command_by_id(commands, "b")

step("Assert the 60px remaining space splits 1:2 (20px/40px) per CSS Grid " +
     "fr-unit semantics (CSS Grid SS11.5, simplified — no minmax(), no " +
     "min-content clamping)")
expect(a.width).to_equal(20)
expect(b.x).to_equal(20)
expect(b.width).to_equal(40)
```

</details>

#### grid-column spans move a cell across tracks

- grid-column spans move a cell across tracks
- Render a 3-column grid where the first cell spans two tracks
- Assert both cells' Draw IR commands were actually emitted
- Assert the spanning cell covers tracks 1-2 (20px) and the auto-placed
   - Expected: a.x equals `grid.x`
   - Expected: a.width equals `20`
   - Expected: b.x equals `a.x + 20`
   - Expected: b.width equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("grid-column spans move a cell across tracks")
step("Render a 3-column grid where the first cell spans two tracks")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff;}" +
    "#grid{display:grid;grid-template-columns:10px 10px 10px;" +
    "width:30px;height:10px;background-color:#e5e7eb;}" +
    "#a{background-color:#ef4444;grid-column:1 / span 2;}" +
    "#b{background-color:#22c55e;}" +
    "</style></head><body><div id='grid'>" +
    "<div id='a'></div><div id='b'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands

step("Assert both cells' Draw IR commands were actually emitted")
assert_true(_draw_ir_index_by_id(commands, "grid") >= 0)
assert_true(_draw_ir_index_by_id(commands, "a") >= 0)
assert_true(_draw_ir_index_by_id(commands, "b") >= 0)

val grid = _draw_ir_command_by_id(commands, "grid")
val a = _draw_ir_command_by_id(commands, "a")
val b = _draw_ir_command_by_id(commands, "b")

step("Assert the spanning cell covers tracks 1-2 (20px) and the auto-placed " +
     "cell lands in track 3")
expect(a.x).to_equal(grid.x)
expect(a.width).to_equal(20)
expect(b.x).to_equal(a.x + 20)
expect(b.width).to_equal(10)
```

</details>

#### gap separates tracks in both axes

- gap separates tracks in both axes
- Render a 3x2 grid with column-gap and row-gap, forcing a wrap to a second row
- Assert all three cells' Draw IR commands were actually emitted
- Assert column-gap widens the spanning cell and offsets the next column,
   - Expected: a.width equals `22`
   - Expected: b.x equals `24`
   - Expected: c.y equals `13`
   - Expected: c.x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gap separates tracks in both axes")
step("Render a 3x2 grid with column-gap and row-gap, forcing a wrap to a second row")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff;}" +
    "#grid{display:grid;grid-template-columns:10px 10px 10px;" +
    "grid-template-rows:10px 10px;column-gap:2px;row-gap:3px;" +
    "width:40px;height:30px;background-color:#e5e7eb;}" +
    "#a{background-color:#ef4444;grid-column:1 / span 2;}" +
    "#b{background-color:#22c55e;}" +
    "#c{background-color:#3b82f6;}" +
    "</style></head><body><div id='grid'>" +
    "<div id='a'></div><div id='b'></div><div id='c'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands

step("Assert all three cells' Draw IR commands were actually emitted")
assert_true(_draw_ir_index_by_id(commands, "a") >= 0)
assert_true(_draw_ir_index_by_id(commands, "b") >= 0)
assert_true(_draw_ir_index_by_id(commands, "c") >= 0)

val a = _draw_ir_command_by_id(commands, "a")
val b = _draw_ir_command_by_id(commands, "b")
val c = _draw_ir_command_by_id(commands, "c")

step("Assert column-gap widens the spanning cell and offsets the next column, " +
     "and row-gap offsets the auto-placed second-row cell")
expect(a.width).to_equal(22)
expect(b.x).to_equal(24)
expect(c.y).to_equal(13)
expect(c.x).to_equal(0)
```

</details>

#### grid-template-areas places named cells

- grid-template-areas places named cells
- Render a grid using a named-area template
- Assert the named-area cell was placed in the 'right' column (x=20),
   - Expected: a.x equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("grid-template-areas places named cells")
step("Render a grid using a named-area template")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff;}" +
    "#grid{display:grid;grid-template-columns:20px 20px;" +
    "grid-template-areas:\"left right\";" +
    "width:40px;height:10px;background-color:#e5e7eb;}" +
    "#a{background-color:#ef4444;grid-area:right;}" +
    "</style></head><body><div id='grid'>" +
    "<div id='a'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands

step("Assert the named-area cell was placed in the 'right' column (x=20), " +
     "resolved via grid_template_area_rects against the parsed " +
     "grid-template-areas template. See " +
     "doc/08_tracking/bug/browser_engine_grid_template_areas_missing_2026-08.md")
assert_true(_draw_ir_index_by_id(commands, "a") >= 0)
val a = _draw_ir_command_by_id(commands, "a")
expect(a.x).to_equal(20)
```

</details>

#### grid-template-areas/grid-area matching is case-sensitive

- grid-template-areas/grid-area matching is case-sensitive
- Render a grid using a mixed-case named-area template and a
- Assert the mixed-case 'Header' reference matches the mixed-case
   - Expected: a.x equals `grid.x`
   - Expected: a.width equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("grid-template-areas/grid-area matching is case-sensitive")
step("Render a grid using a mixed-case named-area template and a " +
     "mixed-case grid-area reference")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff;}" +
    "#grid{display:grid;grid-template-columns:20px 20px;" +
    "grid-template-areas:\"Header Header\";" +
    "width:40px;height:10px;background-color:#e5e7eb;}" +
    "#a{background-color:#ef4444;grid-area:Header;}" +
    "</style></head><body><div id='grid'>" +
    "<div id='a'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands

step("Assert the mixed-case 'Header' reference matches the mixed-case " +
     "'Header' template cells exactly (x=0, width=40, spanning both " +
     "columns) instead of silently falling to auto-placement because " +
     "an earlier .lower() normalization made 'Header' != 'header'. See " +
     "doc/08_tracking/bug/browser_engine_grid_template_areas_missing_2026-08.md")
assert_true(_draw_ir_index_by_id(commands, "grid") >= 0)
assert_true(_draw_ir_index_by_id(commands, "a") >= 0)
val grid = _draw_ir_command_by_id(commands, "grid")
val a = _draw_ir_command_by_id(commands, "a")
expect(a.x).to_equal(grid.x)
expect(a.width).to_equal(40)
```

</details>

#### grid-auto-flow: column fills column-first

- grid-auto-flow: column fills column-first
- Render a 2x2 grid with grid-auto-flow:column and three auto-placed cells
- Assert the third auto-placed cell fills column-first into column 2, row 1
   - Expected: c.x equals `10`
   - Expected: c.y equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("grid-auto-flow: column fills column-first")
step("Render a 2x2 grid with grid-auto-flow:column and three auto-placed cells")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff;}" +
    "#grid{display:grid;grid-template-columns:10px 10px;" +
    "grid-template-rows:10px 10px;grid-auto-flow:column;" +
    "width:20px;height:20px;background-color:#e5e7eb;}" +
    "#a{background-color:#ef4444;}" +
    "#b{background-color:#22c55e;}" +
    "#c{background-color:#3b82f6;}" +
    "</style></head><body><div id='grid'>" +
    "<div id='a'></div><div id='b'></div><div id='c'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands

step("Assert the third auto-placed cell fills column-first into column 2, row 1 " +
     "(x=10,y=0) rather than row-first into row 2, column 1 (x=0,y=10) — " +
     "the auto-placement candidate walk now branches on the parsed " +
     "grid-auto-flow flow mode. See " +
     "doc/08_tracking/bug/browser_engine_grid_template_areas_missing_2026-08.md")
assert_true(_draw_ir_index_by_id(commands, "c") >= 0)
val c = _draw_ir_command_by_id(commands, "c")
expect(c.x).to_equal(10)
expect(c.y).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.3)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-CSS-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8459a34fdbe5ef93b0c127d9c1894a8020196920f0fe382e310340b0ba514865`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8459a34fdbe5ef93b0c127d9c1894a8020196920f0fe382e310340b0ba514865`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8459a34fdbe5ef93b0c127d9c1894a8020196920f0fe382e310340b0ba514865`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/web_css/web_css_grid_spec.spl
mirror: doc/06_spec/03_system/gui/web_css/web_css_grid_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/gui/web_css/web_css_grid_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_css/web_css_grid_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_css/web_css_grid_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/web_css/web_css_grid_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/web_css/web_css_grid_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixed pixel tracks position cells exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_grid_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grid-template-columns: fr tracks split remaining space proportionally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_grid_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grid-column spans move a cell across tracks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
