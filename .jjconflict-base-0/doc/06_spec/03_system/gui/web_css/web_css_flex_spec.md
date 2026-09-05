# Web CSS Flex Layout System Test

> A reader wants to know whether the headless web/HTML-CSS renderer computes

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web CSS Flex Layout System Test

A reader wants to know whether the headless web/HTML-CSS renderer computes

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.2) |
| Source | `test/03_system/gui/web_css/web_css_flex_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A reader wants to know whether the headless web/HTML-CSS renderer computes
CSS flexbox layout correctly: row placement with gap, flex-grow distributing
leftover main-axis space, justify-content pinning items to the container
edges, align-items centering on the cross axis, flex-wrap starting a second
line at the container edge, and order reordering paint without reordering
the DOM.

## Scope and Preconditions

Runs entirely in-process, headless, no display server:
`simple_web_layout_render_html_draw_ir(html, width, height)` produces a
`common.ui.draw_ir.DrawIrComposition`. Every assertion reads computed box
geometry straight off `DrawIrCommand` (`x`/`y`/`width`/`height` = border box)
— never a "didn't crash" check.

## Primary Workflow

Render small fixed HTML/CSS fixtures at a fixed viewport, look up the command
for a named element by `component_id`, and assert exact computed pixel
geometry or paint order.

## Evidence and Provenance

DrawIR-tree oracle per plan §3.6; source:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`.

## Scenarios

### Web CSS flex layout

#### row flex places three items left-to-right with gap

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Flex layout geometry" (expected show, folded, detail, or skip)


- row flex places three items left-to-right with gap
- Render a row flex container with three fixed-width children and a gap
- Assert items are placed left-to-right separated by the gap
   - Expected: a.x equals `row.x`
   - Expected: b.x equals `a.x + a.width + 4`
   - Expected: c.x equals `b.x + b.width + 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("row flex places three items left-to-right with gap")
step("Render a row flex container with three fixed-width children and a gap")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#row{display:flex;flex-direction:row;gap:4px;" +
    "width:60px;height:10px;background-color:#e5e7eb}" +
    "#a{width:10px;height:10px;background-color:#ef4444}" +
    "#b{width:10px;height:10px;background-color:#22c55e}" +
    "#c{width:10px;height:10px;background-color:#3b82f6}" +
    "</style></head><body><div id='row'>" +
    "<div id='a'></div><div id='b'></div><div id='c'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
val row = _draw_ir_command_by_id(commands, "row")
val a = _draw_ir_command_by_id(commands, "a")
val b = _draw_ir_command_by_id(commands, "b")
val c = _draw_ir_command_by_id(commands, "c")

step("Assert items are placed left-to-right separated by the gap")
expect(a.x).to_equal(row.x)
expect(b.x).to_equal(a.x + a.width + 4)
expect(c.x).to_equal(b.x + b.width + 4)
```

</details>

#### flex-grow distributes leftover space proportionally

- flex-grow distributes leftover space proportionally
- Render a row flex container with a fixed item and two grow items 1:2
- Assert leftover 50px space is split roughly 1:2 between g1 and g2, summing exactly
   - Expected: g1.width + g2.width equals `50`
   - Expected: g1.width equals `17`
   - Expected: g2.width equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flex-grow distributes leftover space proportionally")
step("Render a row flex container with a fixed item and two grow items 1:2")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#row{display:flex;flex-direction:row;" +
    "width:60px;height:10px;background-color:#e5e7eb}" +
    "#fixed{width:10px;height:10px;background-color:#000000}" +
    "#g1{flex-grow:1;height:10px;background-color:#ef4444}" +
    "#g2{flex-grow:2;height:10px;background-color:#22c55e}" +
    "</style></head><body><div id='row'>" +
    "<div id='fixed'></div><div id='g1'></div><div id='g2'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
val g1 = _draw_ir_command_by_id(commands, "g1")
val g2 = _draw_ir_command_by_id(commands, "g2")

step("Assert leftover 50px space is split roughly 1:2 between g1 and g2, summing exactly")
expect(g1.width + g2.width).to_equal(50)
expect(g2.width > g1.width).to_be(true)
expect(g1.width).to_equal(17)
expect(g2.width).to_equal(33)
```

</details>

#### justify-content: space-between pins first and last items

- justify-content: space-between pins first and last items
- Render a row flex container with space-between and three items
- Assert the first item sits at the row's start and the last at its end
   - Expected: a.x equals `row.x`
   - Expected: c.x + c.width equals `row.x + row.width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("justify-content: space-between pins first and last items")
step("Render a row flex container with space-between and three items")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#row{display:flex;flex-direction:row;justify-content:space-between;" +
    "width:50px;height:10px;background-color:#e5e7eb}" +
    "#a{width:10px;height:10px;background-color:#ef4444}" +
    "#b{width:10px;height:10px;background-color:#22c55e}" +
    "#c{width:10px;height:10px;background-color:#3b82f6}" +
    "</style></head><body><div id='row'>" +
    "<div id='a'></div><div id='b'></div><div id='c'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
val row = _draw_ir_command_by_id(commands, "row")
val a = _draw_ir_command_by_id(commands, "a")
val c = _draw_ir_command_by_id(commands, "c")

step("Assert the first item sits at the row's start and the last at its end")
expect(a.x).to_equal(row.x)
expect(c.x + c.width).to_equal(row.x + row.width)
```

</details>

#### align-items: center centers cross-axis rects

- align-items: center centers cross-axis rects
- Render a row flex container with align-items:center and a short child
- Assert the short child is centered on the cross (vertical) axis
   - Expected: short.y equals `row.y + (row.height - short.height) / 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("align-items: center centers cross-axis rects")
step("Render a row flex container with align-items:center and a short child")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#row{display:flex;flex-direction:row;align-items:center;" +
    "width:40px;height:30px;background-color:#e5e7eb}" +
    "#short{width:10px;height:10px;background-color:#ef4444}" +
    "</style></head><body><div id='row'>" +
    "<div id='short'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
val row = _draw_ir_command_by_id(commands, "row")
val short = _draw_ir_command_by_id(commands, "short")

step("Assert the short child is centered on the cross (vertical) axis")
expect(short.y).to_equal(row.y + (row.height - short.height) / 2)
```

</details>

#### flex-wrap wraps onto a second line at the container edge

- flex-wrap wraps onto a second line at the container edge
- Render a row flex container too narrow for two 20px items with wrap
- Assert b wrapped onto a second line below a instead of overflowing right
   - Expected: b.x equals `a.x`
- Assert the two 10px-tall line boxes absorbed the container's leftover
   - Expected: a.height equals `10`
   - Expected: b.y equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flex-wrap wraps onto a second line at the container edge")
step("Render a row flex container too narrow for two 20px items with wrap")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#row{display:flex;flex-direction:row;flex-wrap:wrap;" +
    "width:30px;height:40px;background-color:#e5e7eb}" +
    "#a{width:20px;height:10px;background-color:#ef4444}" +
    "#b{width:20px;height:10px;background-color:#22c55e}" +
    "</style></head><body><div id='row'>" +
    "<div id='a'></div><div id='b'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
val a = _draw_ir_command_by_id(commands, "a")
val b = _draw_ir_command_by_id(commands, "b")

step("Assert b wrapped onto a second line below a instead of overflowing right")
expect(b.x).to_equal(a.x)
expect(b.y > a.y).to_be(true)

step("Assert the two 10px-tall line boxes absorbed the container's leftover " +
     "cross-axis space evenly (default align-content: stretch), so the second " +
     "line starts at the stretched 20px line height, not the bare item height")
expect(a.height).to_equal(10)
expect(b.y).to_equal(20)
```

</details>

#### order reorders paint without reordering the DOM

- order reorders paint without reordering the DOM
- Render a row flex container where the DOM-first child is painted last
- Assert the DOM-later, lower-order child is placed before the DOM-first one
   - Expected: second.x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("order reorders paint without reordering the DOM")
step("Render a row flex container where the DOM-first child is painted last")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#row{display:flex;flex-direction:row;" +
    "width:40px;height:10px;background-color:#e5e7eb}" +
    "#first{order:2;width:10px;height:10px;background-color:#ef4444}" +
    "#second{order:1;width:10px;height:10px;background-color:#22c55e}" +
    "</style></head><body><div id='row'>" +
    "<div id='first'></div><div id='second'></div>" +
    "</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
val first = _draw_ir_command_by_id(commands, "first")
val second = _draw_ir_command_by_id(commands, "second")

step("Assert the DOM-later, lower-order child is placed before the DOM-first one")
expect(second.x < first.x).to_be(true)
expect(second.x).to_equal(0)
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

- **Plan:** `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.2)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-CSS-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1673a844b70e559e9d35111aa66b989b2049364f9ff1cb7c984a94cf874d2634`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1673a844b70e559e9d35111aa66b989b2049364f9ff1cb7c984a94cf874d2634`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1673a844b70e559e9d35111aa66b989b2049364f9ff1cb7c984a94cf874d2634`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/web_css/web_css_flex_spec.spl
mirror: doc/06_spec/03_system/gui/web_css/web_css_flex_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/gui/web_css/web_css_flex_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_css/web_css_flex_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_css/web_css_flex_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/web_css/web_css_flex_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/web_css/web_css_flex_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'row flex places three items left-to-right with gap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_flex_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flex-grow distributes leftover space proportionally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_flex_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'justify-content: space-between pins first and last items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
