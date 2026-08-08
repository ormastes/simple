# lab_html_render_spec

> Simple Lab rendered-HTML scenario spec (Stream L, task L2/L4 consumer).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lab_html_render_spec

Simple Lab rendered-HTML scenario spec (Stream L, task L2/L4 consumer).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_lab/lab_html_render_spec.spl` |
| Updated | 2026-08-08 |
| Generator | `simple spipe-docgen` (Simple) |

Simple Lab rendered-HTML scenario spec (Stream L, task L2/L4 consumer).

Drives `app.simple_lab.main.SimpleLabApp` in-process (same widget tree the
HTTP layer serves — see `src/app/simple_lab/lab_server.spl`'s
`LAB_UI_APP`/`LAB_UI_SESSION`) and renders its widget tree through the shared
tree-to-DOM renderer, `app.ui.render.html_widgets.render_html_tree` — the SAME
function `app.ui.web.html.generate_html_page` calls to build the `<div
id="app">` body for a real GET / response (`app.ui.web.server` /
`async_server` / `tls_serve_loop` all call `generate_html_page`, which is
`<!DOCTYPE html>` + head/css/js wrapped around exactly this call). Importing
the full `app.ui.web` module chain here pulls transitive HTTP/server/daemon
plumbing that blows the interpreter's 800-module load budget for a plain unit
spec, so this spec calls the shared tree-renderer directly and wraps it in the
same minimal doctype/head/body shell `generate_html_page` produces, rather
than duplicating any widget-to-HTML logic. This proves the actual rendered
HTML document, not a mock or a screenshot: every assertion below reads real
element tags, ids, and DOM-visible text out of the HTML string the renderer
produced.

Scope note: `SimpleLabApp`'s cell output today is plain captured stdout text
(`LabCellState.output_text`, `main.spl:46`) — there is no markdown or `m{}`
math-block rendering wired into the widget tree yet, so this spec does not
assert a markdown/LaTeX rendering scenario; forcing one would test behavior
that does not exist. See `doc/05_design/app/tools/notebook_lanes_architecture.md`
§7.1 for the current cell-output contract.

Design: doc/05_design/app/tools/notebook_lanes_architecture.md §7.1, §7.4
Plan:   doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md (Stream L)

## Scenarios

### Simple Lab notebook page (rendered HTML)

#### shows a cell editor, a run control, and a lane status indicator on load

- Open a fresh Simple Lab notebook
- Render the notebook's widget tree to HTML the same way the HTTP layer does
   - Expected: evidence.mime equals `text/html`
- Confirm the cell source editor is a real <textarea> element
   - Expected: check_html_has_tag(html, "textarea") is true
   - Expected: html contains `id="cell_0_editor"`
- Confirm a Run control is a real <button> element for that cell
   - Expected: check_html_has_tag(html, "button") is true
   - Expected: html contains `id="cell_0_run"`
   - Expected: check_html_has_element_text(html, "button", "Run") is true
- Confirm the lane/kernel status indicator reads 'not run' before any execution
   - Expected: html contains `id="cell_0_lane_badge"`
   - Expected: check_html_contains_visible_text(html, "not run") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a fresh Simple Lab notebook")
val app = open_notebook_page()

step("Render the notebook's widget tree to HTML the same way the HTTP layer does")
val html = render_page(app)
val evidence = capture_html(
    "Simple Lab fresh notebook page",
    html,
    "cell editor, Run button, lane status",
    ""
)
expect(evidence.mime).to_equal("text/html")

step("Confirm the cell source editor is a real <textarea> element")
expect(check_html_has_tag(html, "textarea")).to_equal(true)
expect(html.contains("id=\"cell_0_editor\"")).to_equal(true)

step("Confirm a Run control is a real <button> element for that cell")
expect(check_html_has_tag(html, "button")).to_equal(true)
expect(html.contains("id=\"cell_0_run\"")).to_equal(true)
expect(check_html_has_element_text(html, "button", "Run")).to_equal(true)

step("Confirm the lane/kernel status indicator reads 'not run' before any execution")
expect(html.contains("id=\"cell_0_lane_badge\"")).to_equal(true)
expect(check_html_contains_visible_text(html, "not run")).to_equal(true)
```

</details>

### Simple Lab notebook page after running a cell

#### shows the executed cell's output in the rendered page

- Open a fresh notebook and type a print statement into the first cell
- Render the page before running — the output element is present but empty
   - Expected: cell_output_element_text(before_html, 0) equals ``
- Run the first cell through the same action the Run button dispatches
- Render the page again and read the cell output back from the DOM
   - Expected: output_check.passed is true
   - Expected: cell_output_element_text(after_html, 0) contains `42 from Simple Lab`
- Confirm the lane status indicator moved from 'not run' to 'available'
   - Expected: check_html_contains_visible_text(after_html, "available") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a fresh notebook and type a print statement into the first cell")
val app = open_notebook_page()
type_into_cell(app, "cell_0_editor", "print(\"42 from Simple Lab\")")

step("Render the page before running — the output element is present but empty")
val before_html = render_page(app)
val before_evidence = capture_html_text("Simple Lab cell before run", before_html, "")
# `cell_0_output` is an always-present `<div id="cell_0_output">` (see
# main.spl's unconditional `text_widget("cell_{index}_output", ...)`),
# so its PRESENCE doesn't distinguish before/after run. And the typed
# source itself contains the literal string "42 from Simple Lab" (the
# print() argument), so whole-page visible text isn't a reliable
# signal either. The real pre-run signal is that this element's own
# content is still empty.
expect(cell_output_element_text(before_html, 0)).to_equal("")

step("Run the first cell through the same action the Run button dispatches")
run_cell_action(app, "cell_run_0")

step("Render the page again and read the cell output back from the DOM")
val after_html = render_page(app)
val output_check = check_html_contains_visible_text_evidence(
    "Simple Lab cell after run",
    after_html,
    "42 from Simple Lab"
)
expect(output_check.passed).to_equal(true)
expect(cell_output_element_text(after_html, 0).contains("42 from Simple Lab")).to_equal(true)

step("Confirm the lane status indicator moved from 'not run' to 'available'")
expect(check_html_contains_visible_text(after_html, "available")).to_equal(true)
```

</details>

### Simple Lab notebook page after adding a cell

#### renders a second cell's editor and run control alongside the first

- Open a fresh notebook with its single starting cell
   - Expected: one_cell_html does not contain `id="cell_1_editor"`
- Add a cell through the '+ Cell' toolbar action
- Render the page and capture it as evidence for the two-cell layout
- Confirm the first cell's editor and run control are still present
   - Expected: two_cell_html contains `id="cell_0_editor"`
   - Expected: two_cell_html contains `id="cell_0_run"`
- Confirm the second cell's editor and run control now exist as distinct elements
   - Expected: two_cell_html contains `id="cell_1_editor"`
   - Expected: two_cell_html contains `id="cell_1_run"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a fresh notebook with its single starting cell")
val app = open_notebook_page()
val one_cell_html = render_page(app)
expect(one_cell_html.contains("id=\"cell_1_editor\"")).to_equal(false)

step("Add a cell through the '+ Cell' toolbar action")
add_cell_action(app)

step("Render the page and capture it as evidence for the two-cell layout")
val two_cell_html = render_page(app)
val _evidence = capture_html(
    "Simple Lab notebook after add-cell",
    two_cell_html,
    "cell_0_editor and cell_1_editor both present",
    ""
)

step("Confirm the first cell's editor and run control are still present")
expect(two_cell_html.contains("id=\"cell_0_editor\"")).to_equal(true)
expect(two_cell_html.contains("id=\"cell_0_run\"")).to_equal(true)

step("Confirm the second cell's editor and run control now exist as distinct elements")
expect(two_cell_html.contains("id=\"cell_1_editor\"")).to_equal(true)
expect(two_cell_html.contains("id=\"cell_1_run\"")).to_equal(true)
```

</details>

### Simple Lab notebook page document shell

#### renders a full HTML document with head and body around the widget tree

- Open a fresh notebook and render its page
- Capture the full page as evidence
- Confirm the document starts with a real HTML5 doctype
- Confirm the document has real <html>, <head>, and <body> elements
   - Expected: check_html_has_tag(html, "html") is true
   - Expected: check_html_has_tag(html, "head") is true
   - Expected: check_html_has_tag(html, "body") is true
- Confirm the cell editor from the widget tree is nested inside that document
   - Expected: html contains `id="cell_0_editor"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a fresh notebook and render its page")
val app = open_notebook_page()
val html = render_page(app)

step("Capture the full page as evidence")
val _evidence = capture_html(
    "Simple Lab full page shell",
    html,
    "doctype, html, head, body wrapping the cell editor",
    ""
)

step("Confirm the document starts with a real HTML5 doctype")
expect(html).to_start_with("<!DOCTYPE html>")

step("Confirm the document has real <html>, <head>, and <body> elements")
expect(check_html_has_tag(html, "html")).to_equal(true)
expect(check_html_has_tag(html, "head")).to_equal(true)
expect(check_html_has_tag(html, "body")).to_equal(true)

step("Confirm the cell editor from the widget tree is nested inside that document")
expect(html.contains("id=\"cell_0_editor\"")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
