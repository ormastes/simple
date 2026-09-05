# Web CSS Table / Replaced-Element / Forms System Test

> A reader wants to know whether the headless web/HTML-CSS renderer lays out

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web CSS Table / Replaced-Element / Forms System Test

A reader wants to know whether the headless web/HTML-CSS renderer lays out

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.8) |
| Source | `test/03_system/gui/web_css/web_css_table_replaced_forms_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A reader wants to know whether the headless web/HTML-CSS renderer lays out
tables (cell grid placement, border-spacing, `table-layout: fixed` column
distribution), replaced elements (`<img>` intrinsic box reservation from
authored `width`/`height`, `object-fit: contain` letterboxing of the painted
image region within its box), form controls (`<button>`/`<input>` intrinsic
padded widget boxes), and `<iframe>` (embedding a child Draw IR subtree at its
own rect).

## Scope and Preconditions

Geometry assertions read `DrawIrCommand.x/y/width/height`/`.content_rect` from
`simple_web_layout_render_html_draw_ir(html, width, height)` (DrawIR-tree
oracle, plan §3.6). The `object-fit` case additionally needs an admitted image
resource, so it uses `simple_web_layout_render_html_draw_ir_with_images` and
reads the distinct `<id>_image` command that carries the letterboxed painted
rect (precedent: `test/03_system/feature/web_platform/css/object_fit_wpt_spec.spl`).
The `iframe` case reads the child batch's `embedding` rect plus a CPU-presenter
pixel readback (precedent:
`test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl`).

## Primary Workflow

Render small fixed HTML/CSS fixtures at a fixed viewport, look up the command
for a named element by `component_id`, and assert exact computed geometry.

## Evidence and Provenance

DrawIR-tree oracle + admitted-image oracle + iframe embedding/pixel oracle per
plan §3.6; source:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
`simple_web_html_layout_renderer_layout.spl` (table row/cell placement),
`simple_web_html_layout_renderer_paint_layout.spl` (`object-fit` letterboxing).

## Known gap (RED-by-design)

`doc/08_tracking/bug/browser_engine_table_row_horizontal_layout_2026-07-11.md`
was filed for `<tr>` children stacking vertically instead of flowing
horizontally; that specific symptom is now fixed (a single `<tr>` with two
`<td>` children places both cells on one row, tested indirectly by this file's
first `it`'s first row). Investigating this unit's assertions surfaced a
**different, still-open** defect in the same area: a table with **two or more
`<tr>` rows** drops cells outright — only the table's first cell renders with
real geometry; every other cell (including the rest of row 1 once a second row
exists, and all of row 2) collapses to a 1px-tall row with no cell children in
the Draw IR at all. This is filed as a repro update to the same bug doc (see
that file's "Update 2026-08-08" section). The two `it`s below that need a
multi-row grid assert the CSS-correct expected geometry and are RED against
that open defect; this is the intended workflow (see plan unit notes), not a
weakened test.

## Scenarios

### Web CSS table, replaced-element, and forms layout

#### a 2x2 table places cells in a grid with border-spacing

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Table, replaced element, and forms layout" (expected show, folded, detail, or skip)


- a 2x2 table places cells in a grid with border-spacing
- Render a 2x2 table with 4px border-spacing and 10x10 cells
- Assert the first cell is offset by the table's border-spacing on both axes
   - Expected: a.x equals `4`
   - Expected: a.y equals `4`
- RED-by-design: the second cell of row 1 should sit to the right of the first cell plus one border-spacing gap (open bug: browser_engine_table_row_horizontal_layout_2026-07-11.md, this file's repro appended there)
   - Expected: b.x equals `a.x + a.width + 4`
   - Expected: b.y equals `a.y`
- RED-by-design: row 2 should sit below row 1 at real cell height, not collapse to a 1px placeholder
- RED-by-design: row 2's first cell should render with real content geometry


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a 2x2 table places cells in a grid with border-spacing")
step("Render a 2x2 table with 4px border-spacing and 10x10 cells")
val html = (
    "<html><head><style>" +
    "html{margin:0;padding:0}body{margin:0;padding:0}" +
    "table{border-spacing:4px}td{width:10px;height:10px}" +
    "</style></head><body><table id='t'>" +
    "<tr id='r1'><td id='a'>A</td><td id='b'>B</td></tr>" +
    "<tr id='r2'><td id='c'>C</td><td id='d'>D</td></tr>" +
    "</table></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 200, 200)
val commands = composition.batches[0].commands
val a = _draw_ir_command_by_id(commands, "a")
val b = _draw_ir_command_by_id(commands, "b")
val r2 = _draw_ir_command_by_id(commands, "r2")
val c = _draw_ir_command_by_id(commands, "c")

step("Assert the first cell is offset by the table's border-spacing on both axes")
expect(a.x).to_equal(4)
expect(a.y).to_equal(4)

step("RED-by-design: the second cell of row 1 should sit to the right of the first cell plus one border-spacing gap (open bug: browser_engine_table_row_horizontal_layout_2026-07-11.md, this file's repro appended there)")
expect(b.x).to_equal(a.x + a.width + 4)
expect(b.y).to_equal(a.y)

step("RED-by-design: row 2 should sit below row 1 at real cell height, not collapse to a 1px placeholder")
expect(r2.height).to_be_greater_than(1)

step("RED-by-design: row 2's first cell should render with real content geometry")
expect(c.width).to_be_greater_than(0)
```

</details>

#### table-layout: fixed distributes columns by first row

- table-layout: fixed distributes columns by first row
- Render a 2-row table-layout:fixed table where column widths must come from row 1
- Assert row 1's two columns split the 100px table evenly (fixed layout ignores content length)
   - Expected: a2.x equals `0`
   - Expected: a2.width equals `50`
   - Expected: b2.x equals `50`
   - Expected: b2.width equals `50`
- RED-by-design: row 2 should reuse the same fixed column grid as row 1 (open bug: browser_engine_table_row_horizontal_layout_2026-07-11.md)
   - Expected: c2.width equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("table-layout: fixed distributes columns by first row")
step("Render a 2-row table-layout:fixed table where column widths must come from row 1")
val html = (
    "<html><head><style>" +
    "html{margin:0;padding:0}body{margin:0;padding:0}" +
    "table{table-layout:fixed;width:100px;border-spacing:0}" +
    "</style></head><body><table id='t2'>" +
    "<tr id='r1'><td id='a2'>AAAAAAAAAA</td><td id='b2'>B</td></tr>" +
    "<tr id='r2'><td id='c2'>C</td><td id='d2'>D</td></tr>" +
    "</table></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 200, 200)
val commands = composition.batches[0].commands
val a2 = _draw_ir_command_by_id(commands, "a2")
val b2 = _draw_ir_command_by_id(commands, "b2")

step("Assert row 1's two columns split the 100px table evenly (fixed layout ignores content length)")
expect(a2.x).to_equal(0)
expect(a2.width).to_equal(50)
expect(b2.x).to_equal(50)
expect(b2.width).to_equal(50)

step("RED-by-design: row 2 should reuse the same fixed column grid as row 1 (open bug: browser_engine_table_row_horizontal_layout_2026-07-11.md)")
val c2 = _draw_ir_command_by_id(commands, "c2")
expect(c2.width).to_equal(50)
```

</details>

#### img with width/height reserves the replaced box

- img with width/height reserves the replaced box
- Render an img with authored width/height attributes and no CSS size
- Assert the replaced box reserves exactly the authored intrinsic dimensions
   - Expected: i.x equals `0`
   - Expected: i.y equals `0`
   - Expected: i.width equals `30`
   - Expected: i.height equals `20`
   - Expected: i.content_rect.width equals `30`
   - Expected: i.content_rect.height equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("img with width/height reserves the replaced box")
step("Render an img with authored width/height attributes and no CSS size")
val html = (
    "<html><head><style>html{margin:0;padding:0}body{margin:0;padding:0}" +
    "</style></head><body><img id='i' src='x.png' width='30' height='20'></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 200, 200)
val i = _draw_ir_command_by_id(composition.batches[0].commands, "i")

step("Assert the replaced box reserves exactly the authored intrinsic dimensions")
expect(i.x).to_equal(0)
expect(i.y).to_equal(0)
expect(i.width).to_equal(30)
expect(i.height).to_equal(20)
expect(i.content_rect.width).to_equal(30)
expect(i.content_rect.height).to_equal(20)
```

</details>

#### object-fit: contain letterboxes an image in its box

- object-fit: contain letterboxes an image in its box
- Admit a 2x4 portrait image into an 8x8 box with object-fit:contain
- Assert the layout box keeps its authored square dimensions
   - Expected: box.width equals `8`
   - Expected: box.height equals `8`
- Assert the painted image region is letterboxed to the portrait ratio and centered
   - Expected: painted.width equals `4`
   - Expected: painted.height equals `8`
   - Expected: painted.x equals `2`
   - Expected: painted.y equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("object-fit: contain letterboxes an image in its box")
step("Admit a 2x4 portrait image into an 8x8 box with object-fit:contain")
val html = (
    "<html><head><style>html{margin:0;padding:0}body{margin:0;padding:0}" +
    "#i{display:block;width:8px;height:8px;object-fit:contain;" +
    "object-position:50% 50%}" +
    "</style></head><body><img id='i' src='image://tall'></body></html>"
)
val image = simpleos_host_gpu_image_resource(
    "image://tall", 2, 4, [0xFFDC2626u32; 8]
)
val composition = simple_web_layout_render_html_draw_ir_with_images(
    html, 20, 20, [image]
)
val commands = composition.batches[0].commands
val box = _draw_ir_command_by_id(commands, "i")
val painted = _draw_ir_command_by_id(commands, "i_image")

step("Assert the layout box keeps its authored square dimensions")
expect(box.width).to_equal(8)
expect(box.height).to_equal(8)

step("Assert the painted image region is letterboxed to the portrait ratio and centered")
expect(painted.width).to_equal(4)
expect(painted.height).to_equal(8)
expect(painted.x).to_equal(2)
expect(painted.y).to_equal(0)
```

</details>

#### button and input render intrinsic widget boxes

- button and input render intrinsic widget boxes
- Render an unsized button and text input side by side
- Assert the button grew its border-box by its own padding around the label content
   - Expected: btn.x equals `0`
   - Expected: btn.width equals `33`
   - Expected: btn.content_rect.x equals `6`
   - Expected: btn.content_rect.width equals `21`
- Assert the input sits to the right of the button and reserves its own padded box
   - Expected: inp.x equals `btn.x + btn.width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("button and input render intrinsic widget boxes")
step("Render an unsized button and text input side by side")
val html = (
    "<html><head><style>html{margin:0;padding:0}body{margin:0;padding:0}" +
    "</style></head><body><button id='btn'>OK</button>" +
    "<input id='inp' value='hi'></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 200, 200)
val commands = composition.batches[0].commands
val btn = _draw_ir_command_by_id(commands, "btn")
val inp = _draw_ir_command_by_id(commands, "inp")

step("Assert the button grew its border-box by its own padding around the label content")
expect(btn.x).to_equal(0)
expect(btn.width).to_equal(33)
expect(btn.content_rect.x).to_equal(6)
expect(btn.content_rect.width).to_equal(21)

step("Assert the input sits to the right of the button and reserves its own padded box")
expect(inp.x).to_equal(btn.x + btn.width)
assert_true(inp.width > 0)
assert_true(inp.height > 0)
```

</details>

#### iframe embeds a child DrawIR subtree at its rect

- iframe embeds a child DrawIR subtree at its rect
- Render a red marker box followed by a block iframe with green srcdoc content
- Assert the iframe's own box sits below the marker at its authored dimensions
   - Expected: f.x equals `0`
   - Expected: f.y equals `5`
   - Expected: f.width equals `16`
   - Expected: f.height equals `12`
- Assert a distinct child batch is embedded at the iframe's rect
   - Expected: child.embedding.x equals `0`
   - Expected: child.embedding.y equals `5`
- Assert the composited pixels show the marker, the embedded srcdoc background, and the outer body background
   - Expected: pixels[2 + 2 * 40] equals `0xFFEF4444u32`
   - Expected: pixels[10 + 8 * 40] equals `0xFF22C55Eu32`
   - Expected: pixels[35 + 25 * 40] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iframe embeds a child DrawIR subtree at its rect")
step("Render a red marker box followed by a block iframe with green srcdoc content")
val html = (
    "<html><body style='margin:0;padding:0;background-color:#ffffff'>" +
    "<div id='left' style='width:5px;height:5px;background-color:#ef4444'></div>" +
    "<iframe id='f' width='16' height='12' style='display:block' " +
    "srcdoc=\"&lt;body style='margin:0;background-color:#22c55e'&gt;&lt;/body&gt;\">" +
    "</iframe></body></html>"
)
val result = simple_web_layout_render_html_draw_ir_result(html, 40, 30)
val f = _draw_ir_command_by_id(result.composition.batches[0].commands, "f")

step("Assert the iframe's own box sits below the marker at its authored dimensions")
expect(f.x).to_equal(0)
expect(f.y).to_equal(5)
expect(f.width).to_equal(16)
expect(f.height).to_equal(12)

step("Assert a distinct child batch is embedded at the iframe's rect")
val child_index = _iframe_child_batch_index(result.composition)
expect(child_index).to_be_greater_than(0)
val child = result.composition.batches[child_index]
expect(child.embedding.x).to_equal(0)
expect(child.embedding.y).to_equal(5)

step("Assert the composited pixels show the marker, the embedded srcdoc background, and the outer body background")
val pixels = simple_web_render_draw_ir_composition_with_cpu_backend(
    result.composition, 40, 30
)
expect(pixels[2 + 2 * 40]).to_equal(0xFFEF4444u32)
expect(pixels[10 + 8 * 40]).to_equal(0xFF22C55Eu32)
expect(pixels[35 + 25 * 40]).to_equal(0xFFFFFFFFu32)
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


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.8)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-CSS-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e96acd242d8d65072363df92adefb2de8107dab218a924d33f4be2485c14de3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e96acd242d8d65072363df92adefb2de8107dab218a924d33f4be2485c14de3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e96acd242d8d65072363df92adefb2de8107dab218a924d33f4be2485c14de3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/web_css/web_css_table_replaced_forms_spec.spl
mirror: doc/06_spec/03_system/gui/web_css/web_css_table_replaced_forms_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/gui/web_css/web_css_table_replaced_forms_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_css/web_css_table_replaced_forms_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_css/web_css_table_replaced_forms_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 29 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/web_css/web_css_table_replaced_forms_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/web_css/web_css_table_replaced_forms_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a 2x2 table places cells in a grid with border-spacing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_table_replaced_forms_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'table-layout: fixed distributes columns by first row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_table_replaced_forms_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'img with width/height reserves the replaced box' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
