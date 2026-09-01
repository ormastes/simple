# Web CSS Box Model System Test

> A reader wants to know whether the headless web/HTML-CSS renderer computes the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web CSS Box Model System Test

A reader wants to know whether the headless web/HTML-CSS renderer computes the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.1) |
| Source | `test/03_system/gui/web_css/web_css_box_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A reader wants to know whether the headless web/HTML-CSS renderer computes the
CSS box model correctly: margins offsetting siblings, padding growing the
painted (border) box while leaving the content box untouched, box-sizing:
border-box holding the outer width fixed while shrinking the content box,
min/max-width clamping, overflow: hidden clipping a child's Draw IR to its
parent's box, and aspect-ratio deriving one box dimension from the other.

## Scope and Preconditions

Runs entirely in-process, headless, no display server:
`simple_web_layout_render_html_draw_ir(html, width, height)` produces a
`common.ui.draw_ir.DrawIrComposition`. Every assertion reads computed box
geometry straight off `DrawIrCommand` (`x`/`y`/`width`/`height` = border box,
`content_rect` = content box, `clip_rect` = the ancestor-clip region applied
at paint time) — never a "didn't crash" check.

## Primary Workflow

Render small fixed HTML/CSS fixtures at a fixed viewport, look up the command
for a named element by `component_id`, and assert exact computed pixel
geometry.

## Evidence and Provenance

DrawIR-tree oracle per plan §3.6; source:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`.

## Scenarios

### Web CSS box model

#### margins offset a block from its parent and siblings

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Box model geometry" (expected show, folded, detail, or skip)


- margins offset a block from its parent and siblings
- Render two blocks: a top/left/right margin, b a top/left margin only
- Assert a is offset from the body edge by its own margin
   - Expected: a.x equals `4`
   - Expected: a.y equals `4`
- Assert b is offset from a by b's own top/left margin
   - Expected: b.x equals `5`
   - Expected: b.y equals `a.y + a.height + 6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("margins offset a block from its parent and siblings")
step("Render two blocks: a top/left/right margin, b a top/left margin only")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#a{display:block;width:10px;height:10px;" +
    "margin:4px 4px 0 4px;background-color:#ef4444}" +
    "#b{display:block;width:10px;height:10px;" +
    "margin:6px 0 0 5px;background-color:#22c55e}" +
    "</style></head><body><div id='a'></div><div id='b'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
val a = _draw_ir_command_by_id(commands, "a")
val b = _draw_ir_command_by_id(commands, "b")

step("Assert a is offset from the body edge by its own margin")
expect(a.x).to_equal(4)
expect(a.y).to_equal(4)

step("Assert b is offset from a by b's own top/left margin")
expect(b.x).to_equal(5)
expect(b.y).to_equal(a.y + a.height + 6)
```

</details>

#### padding grows the painted background but not the content box

- padding grows the painted background but not the content box
- Render a block with 5px padding on all sides
- Assert the painted (border) box grew by padding on both axes
   - Expected: c.width equals `30`
   - Expected: c.height equals `22`
- Assert the content box kept the authored content width/height
   - Expected: c.content_rect.width equals `20`
   - Expected: c.content_rect.height equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("padding grows the painted background but not the content box")
step("Render a block with 5px padding on all sides")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#c{display:block;width:20px;height:12px;padding:5px;" +
    "background-color:#3b82f6}" +
    "</style></head><body><div id='c'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val c = _draw_ir_command_by_id(composition.batches[0].commands, "c")

step("Assert the painted (border) box grew by padding on both axes")
expect(c.width).to_equal(30)
expect(c.height).to_equal(22)

step("Assert the content box kept the authored content width/height")
expect(c.content_rect.width).to_equal(20)
expect(c.content_rect.height).to_equal(12)
```

</details>

#### box-sizing: border-box keeps the outer width fixed

- box-sizing: border-box keeps the outer width fixed
- Render a block with padding+border under box-sizing:border-box
- Assert the outer (border) box stayed exactly the authored width
   - Expected: d.width equals `40`
   - Expected: d.height equals `20`
- Assert the content box shrank to absorb padding + border
   - Expected: d.content_rect.width equals `40 - 2 * 5 - 2 * 2`
   - Expected: d.content_rect.height equals `20 - 2 * 5 - 2 * 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("box-sizing: border-box keeps the outer width fixed")
step("Render a block with padding+border under box-sizing:border-box")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#d{display:block;width:40px;height:20px;padding:5px;" +
    "border:2px solid #000000;box-sizing:border-box;" +
    "background-color:#111827}" +
    "</style></head><body><div id='d'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val d = _draw_ir_command_by_id(composition.batches[0].commands, "d")

step("Assert the outer (border) box stayed exactly the authored width")
expect(d.width).to_equal(40)
expect(d.height).to_equal(20)

step("Assert the content box shrank to absorb padding + border")
expect(d.content_rect.width).to_equal(40 - 2 * 5 - 2 * 2)
expect(d.content_rect.height).to_equal(20 - 2 * 5 - 2 * 2)
```

</details>

#### min- and max-width clamp an over- and under-sized block

- min- and max-width clamp an over- and under-sized block
- Render an undersized block clamped up by min-width
- Assert the width was clamped up to min-width
   - Expected: e.width equals `20`
- Render an oversized block clamped down by max-width
- Assert the width was clamped down to max-width
   - Expected: f.width equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("min- and max-width clamp an over- and under-sized block")
step("Render an undersized block clamped up by min-width")
val html_min = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#e{display:block;width:5px;height:10px;min-width:20px;" +
    "background-color:#000000}" +
    "</style></head><body><div id='e'></div></body></html>"
)
val composition_min = simple_web_layout_render_html_draw_ir(html_min, 64, 64)
val e = _draw_ir_command_by_id(composition_min.batches[0].commands, "e")

step("Assert the width was clamped up to min-width")
expect(e.width).to_equal(20)

step("Render an oversized block clamped down by max-width")
val html_max = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#f{display:block;width:500px;max-width:50px;height:10px;" +
    "background-color:#000000}" +
    "</style></head><body><div id='f'></div></body></html>"
)
val composition_max = simple_web_layout_render_html_draw_ir(html_max, 600, 64)
val f = _draw_ir_command_by_id(composition_max.batches[0].commands, "f")

step("Assert the width was clamped down to max-width")
expect(f.width).to_equal(50)
```

</details>

#### overflow: hidden clips a child's DrawIR to the parent rect

- overflow: hidden clips a child's DrawIR to the parent rect
- Render a narrow overflow:hidden shell around a wider child
- Assert the child's own painted box kept its full authored width
   - Expected: wide.width equals `30`
- Assert the child's clip rect was narrowed to the shell's box
   - Expected: wide.clip_rect.x equals `shell.x`
   - Expected: wide.clip_rect.y equals `shell.y`
   - Expected: wide.clip_rect.width equals `shell.width`
   - Expected: wide.clip_rect.height equals `shell.height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overflow: hidden clips a child's DrawIR to the parent rect")
step("Render a narrow overflow:hidden shell around a wider child")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#shell{display:block;overflow:hidden;width:12px;height:8px;" +
    "background-color:#e5e7eb}" +
    "#wide{display:block;width:30px;height:6px;" +
    "background-color:#ef4444}" +
    "</style></head><body><section id='shell'>" +
    "<div id='wide'></div></section></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val shell = _draw_ir_command_by_id(composition.batches[0].commands, "shell")
val wide = _draw_ir_command_by_id(composition.batches[0].commands, "wide")

step("Assert the child's own painted box kept its full authored width")
expect(wide.width).to_equal(30)

step("Assert the child's clip rect was narrowed to the shell's box")
expect(wide.clip_rect.present).to_be(true)
expect(wide.clip_rect.x).to_equal(shell.x)
expect(wide.clip_rect.y).to_equal(shell.y)
expect(wide.clip_rect.width).to_equal(shell.width)
expect(wide.clip_rect.height).to_equal(shell.height)
```

</details>

#### aspect-ratio derives height from width

- aspect-ratio derives height from width
- Render a block with only a width and an aspect-ratio declared
- Assert height was derived from width using the declared ratio
   - Expected: g.width equals `40`
   - Expected: g.height equals `20`
   - Expected: h.width equals `32`
   - Expected: h.height equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aspect-ratio derives height from width")
step("Render a block with only a width and an aspect-ratio declared")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#g{display:block;width:40px;aspect-ratio:2/1;" +
    "background-color:#000000}" +
    "#h{display:block;width:32px;aspect-ratio:16/9;" +
    "background-color:#000000}" +
    "</style></head><body><div id='g'></div><div id='h'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 128)
val g = _draw_ir_command_by_id(composition.batches[0].commands, "g")
val h = _draw_ir_command_by_id(composition.batches[0].commands, "h")

step("Assert height was derived from width using the declared ratio")
expect(g.width).to_equal(40)
expect(g.height).to_equal(20)
expect(h.width).to_equal(32)
expect(h.height).to_equal(18)
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

- **Plan:** `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-CSS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5c096dcd3490fbe139893d65d5e1939d5fb779b99a108f995a7c436d679609fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c096dcd3490fbe139893d65d5e1939d5fb779b99a108f995a7c436d679609fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c096dcd3490fbe139893d65d5e1939d5fb779b99a108f995a7c436d679609fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/web_css/web_css_box_model_spec.spl
mirror: doc/06_spec/03_system/gui/web_css/web_css_box_model_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/gui/web_css/web_css_box_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_css/web_css_box_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_css/web_css_box_model_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/web_css/web_css_box_model_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/web_css/web_css_box_model_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'margins offset a block from its parent and siblings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_box_model_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'padding grows the painted background but not the content box' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_box_model_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'box-sizing: border-box keeps the outer width fixed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
