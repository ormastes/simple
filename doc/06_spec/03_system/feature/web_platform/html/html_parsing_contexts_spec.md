# Canonical HTML Parsing Contexts

> Proves one canonical tokenizer/tree-builder projection feeds Web semantic

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Canonical HTML Parsing Contexts

Proves one canonical tokenizer/tree-builder projection feeds Web semantic

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/html_parsing_contexts_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves one canonical tokenizer/tree-builder projection feeds Web semantic
layout, Draw IR, and Engine2D for context-sensitive HTML.

## Scenarios

### Production canonical HTML parsing contexts

#### should auto-close a paragraph before a block sibling

- Repair paragraph parentage in canonical BeDOM
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
- Preserve sibling geometry in Web layout and Draw IR
   - Protocol capture: after_step
- Render both canonical sibling boxes
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: pixels[15] equals `0xFFDC2626u32`
   - Expected: pixels[15 + 8 * 16] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body id='body' style='margin:0'>" +
    "<p id='paragraph' style='margin:0;width:16px;height:8px;" +
    "background:#dc2626'><div id='after' style='width:16px;" +
    "height:8px;background:#2563eb'></div></body></html>"
)

step("Repair paragraph parentage in canonical BeDOM")
_expect_bedom_parent(html, "paragraph", "body")
_expect_bedom_parent(html, "after", "body")

step("Preserve sibling geometry in Web layout and Draw IR")
val result = simple_web_layout_render_html_draw_ir_result(html, 16, 16)
expect(simple_web_layout_debug_layout_by_id(
    html, 16, 16, "after", "y"
)).to_equal("8")
expect(_command_by_id(
    result.composition, "paragraph"
).parent_id).to_equal("body")
expect(_command_by_id(
    result.composition, "after"
).parent_id).to_equal("body")

step("Render both canonical sibling boxes")
val pixels = _pixels(html, 16, 16)
expect(pixels[15]).to_equal(0xFFDC2626u32)
expect(pixels[15 + 8 * 16]).to_equal(0xFF2563EBu32)
```

</details>

#### should foster a nonempty subtree before its table

- Build canonical BeDOM foster parentage with nested text
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
- foster path[foster path len
   - Protocol capture: after_step
- Project the same parentage and geometry into Web layout
   - Protocol capture: after_step
- Lower the foster subtree through Draw IR and pixels
   - Protocol capture: after_step
   - Evidence: protocol response verified by 7 expected checks
   - Expected: foster.parent_id equals `body`
   - Expected: table.parent_id equals `body`
   - Expected: _has_text(result.composition, "FOSTER") is true
   - Expected: foster.y equals `0`
   - Expected: table.y equals `8`
   - Expected: pixels[31] equals `0xFF16A34Au32`
   - Expected: pixels[31 + 8 * 32] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body id='body' style='margin:0'>" +
    "<table id='table' style='width:32px;height:8px;" +
    "background:#2563eb'><div id='foster' style='width:32px;" +
    "height:8px;background:#16a34a'><span id='nested'>" +
    "FOSTER</span></div></table></body></html>"
)

step("Build canonical BeDOM foster parentage with nested text")
_expect_bedom_parent(html, "foster", "body")
_expect_bedom_parent(html, "table", "body")
_expect_bedom_parent(html, "nested", "foster")
val foster_path = _path(html, "foster")
expect(be_dom_get_text_content(
    foster_path[foster_path.len() - 1]
)).to_equal("FOSTER")

step("Project the same parentage and geometry into Web layout")
val result = simple_web_layout_render_html_draw_ir_result(html, 32, 16)
expect(simple_web_layout_debug_layout_by_id(
    html, 32, 16, "foster", "y"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    html, 32, 16, "table", "y"
)).to_equal("8")

step("Lower the foster subtree through Draw IR and pixels")
val foster = _command_by_id(result.composition, "foster")
val table = _command_by_id(result.composition, "table")
expect(foster.parent_id).to_equal("body")
expect(table.parent_id).to_equal("body")
expect(_source_kind_for(
    result.composition, "foster"
)).to_equal("html_ast")
expect(_has_text(result.composition, "FOSTER")).to_equal(true)
expect(foster.y).to_equal(0)
expect(table.y).to_equal(8)
val pixels = _pixels(html, 32, 16)
expect(pixels[31]).to_equal(0xFF16A34Au32)
expect(pixels[31 + 8 * 32]).to_equal(0xFF2563EBu32)
```

</details>

#### should foster non-whitespace table text in exact source order

- Foster text and element siblings before the canonical table
   - Protocol capture: after_step
   - Evidence: protocol response verified by 5 expected checks
   - Expected: body.children.len() equals `4`
   - Expected: body.children[0].data equals `FIRST`
   - Expected: body.children[1].get_attr("id") equals `middle`
   - Expected: body.children[2].data equals `LAST`
   - Expected: body.children[3].get_attr("id") equals `table`
- Keep the same ordering through Web layout and Draw IR
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: _has_text(result.composition, "FIRST") is true
   - Expected: _has_text(result.composition, "MIDDLE") is true
   - Expected: _has_text(result.composition, "LAST") is true
-  command by id
   - Protocol capture: after_step
- Render the fostered element before the table
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: pixels contains `0xFF16A34Au32`
   - Expected: pixels contains `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body id='body' style='margin:0'>" +
    "<table id='table' style='width:32px;height:8px;" +
    "background:#2563eb'>FIRST<span id='middle' style='display:block;" +
    "width:32px;height:8px;background:#16a34a'>MIDDLE</span>" +
    "LAST</table></body></html>"
)

step("Foster text and element siblings before the canonical table")
val body_path = _path(html, "body")
val body = body_path[body_path.len() - 1]
expect(body.children.len()).to_equal(4)
expect(body.children[0].data).to_equal("FIRST")
expect(body.children[1].get_attr("id")).to_equal("middle")
expect(body.children[2].data).to_equal("LAST")
expect(body.children[3].get_attr("id")).to_equal("table")

step("Keep the same ordering through Web layout and Draw IR")
val result = simple_web_layout_render_html_draw_ir_result(html, 32, 32)
expect(_has_text(result.composition, "FIRST")).to_equal(true)
expect(_has_text(result.composition, "MIDDLE")).to_equal(true)
expect(_has_text(result.composition, "LAST")).to_equal(true)
expect(_command_by_id(
    result.composition, "table"
).y).to_be_greater_than(
    _command_by_id(result.composition, "middle").y
)

step("Render the fostered element before the table")
val pixels = _pixels(html, 32, 32)
expect(pixels.contains(0xFF16A34Au32)).to_equal(true)
expect(pixels.contains(0xFF2563EBu32)).to_equal(true)
```

</details>

#### should accept uppercase textarea close and reject a prefix close

- Keep the false closer and markup as canonical textarea text
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
- editor path[editor path len
   - Protocol capture: after_step
- html tree builder build
   - Protocol capture: after_step
- Resume Web layout only after the exact uppercase closer
   - Protocol capture: after_step
- Lower literal RCDATA and its following sibling
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: editor.parent_id equals `body`
   - Expected: after.parent_id equals `body`
   - Expected: after.y equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body id='body' style='margin:0'>" +
    "<textarea id='editor' style='display:block;width:48px;" +
    "height:12px;background:#fef3c7'>alpha</textareaevil>" +
    "<b>x</b></TEXTAREA><div id='after' style='width:48px;" +
    "height:4px;background:#2563eb'></div></body></html>"
)

step("Keep the false closer and markup as canonical textarea text")
_expect_bedom_parent(html, "editor", "body")
_expect_bedom_parent(html, "after", "body")
val editor_path = _path(html, "editor")
expect(be_dom_get_text_content(
    editor_path[editor_path.len() - 1]
)).to_contain("</textareaevil><b>x</b>")
expect(be_dom_find_by_tag(
    html_tree_builder_build(html), "b"
).len()).to_equal(0)

step("Resume Web layout only after the exact uppercase closer")
val result = simple_web_layout_render_html_draw_ir_result(html, 48, 16)
expect(simple_web_layout_debug_layout_by_id(
    html, 48, 16, "after", "y"
)).to_equal("12")

step("Lower literal RCDATA and its following sibling")
val editor = _command_by_id(result.composition, "editor")
val after = _command_by_id(result.composition, "after")
expect(editor.parent_id).to_equal("body")
expect(after.parent_id).to_equal("body")
expect(_source_kind_for(
    result.composition, "editor"
)).to_equal("html_ast")
expect(_has_text(
    result.composition, "</textareaevil><b>x</b>"
)).to_equal(true)
expect(after.y).to_equal(12)
expect(_pixels(html, 48, 16)[47 + 12 * 48]).to_equal(
    0xFF2563EBu32
)
```

</details>

#### should synthesize html and body independently

- Build both independently omitted structures in canonical BeDOM
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: missing_body_nodes.len() equals `1`
- missing body main len
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: missing_html_nodes.len() equals `1`
- Preserve implicit structure and stable IDs in Web layout
   - Protocol capture: after_step
- Keep canonical generated component order through Draw IR
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: _pixels(missing_body, 16, 8)[15] equals `0xFF7C3AEDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_body = (
    "<html id='document'><main id='main' style='width:16px;" +
    "height:8px;background:#7c3aed'></main></html>"
)
val missing_html = (
    "<body id='page' style='margin:0'><main id='main' " +
    "style='width:16px;height:8px;background:#7c3aed'>" +
    "前&#x4E2D;後</main>" +
    "</body>"
)

step("Build both independently omitted structures in canonical BeDOM")
val missing_body_dom = html_tree_builder_build(missing_body)
val missing_body_nodes = be_dom_find_by_tag(missing_body_dom, "body")
val missing_body_main = _path(missing_body, "main")
expect(missing_body_nodes.len()).to_equal(1)
expect(missing_body_main[
    missing_body_main.len() - 2
].node_id).to_equal(missing_body_nodes[0].node_id)
val missing_html_dom = html_tree_builder_build(missing_html)
val missing_html_nodes = be_dom_find_by_tag(missing_html_dom, "html")
val page_path = _path(missing_html, "page")
expect(missing_html_nodes.len()).to_equal(1)
expect(page_path[page_path.len() - 2].node_id).to_equal(
    missing_html_nodes[0].node_id
)

step("Preserve implicit structure and stable IDs in Web layout")
val body_result = simple_web_layout_render_html_draw_ir_result(
    missing_body, 16, 8
)
val html_result = simple_web_layout_render_html_draw_ir_result(
    missing_html, 16, 8
)
expect(simple_web_layout_debug_layout_by_id(
    missing_body, 16, 8, "main", "width"
)).to_equal("16")
expect(simple_web_layout_debug_layout_by_id(
    missing_html, 16, 8, "main", "height"
)).to_equal("8")

step("Keep canonical generated component order through Draw IR")
expect(_command_by_id(
    body_result.composition, "main"
).parent_id).to_equal("body_2")
expect(_command_by_id(
    html_result.composition, "main"
).parent_id).to_equal("page")
expect(_has_text(
    html_result.composition, "前中後"
)).to_equal(true)
expect(_pixels(missing_body, 16, 8)[15]).to_equal(0xFF7C3AEDu32)
expect(_pixels(
    missing_html, 16, 8
).contains(0xFF7C3AEDu32)).to_equal(true)
```

</details>

#### should keep template content inert despite authored CSS

- Retain inert template semantics in canonical BeDOM
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
- Force template inertness after the authored CSS cascade
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: plan.script_blocks.len() equals `0`
   - Expected: plan.style_sources.len() equals `1`
   - Expected: plan.image_sources.len() equals `0`
- Omit inert commands and pixels from Draw IR execution
   - Protocol capture: after_step
   - Evidence: protocol response verified by 4 expected checks
   - Expected: _has_command(result.composition, "hidden") is false
   - Expected: _has_text(result.composition, "HIDDEN") is false
   - Expected: pixels[15] equals `0xFF16A34Au32`
   - Expected: pixels does not contain `0xFFDC2626u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body id='body' style='margin:0'>" +
    "<style>template{display:block!important}" +
    "#hidden{display:block!important}</style>" +
    "<template id='template' style='display:block!important'>" +
    "<script src='/hidden.js'></script>" +
    "<style>#visible{display:none!important}</style>" +
    "<link rel='stylesheet' href='/hidden.css'>" +
    "<img src='/hidden.png'>" +
    "<div id='hidden' style='display:block!important;width:16px;" +
    "height:8px;background:#dc2626'>HIDDEN</div></template>" +
    "<div id='visible' style='width:16px;height:8px;" +
    "background:#16a34a'></div></body></html>"
)

step("Retain inert template semantics in canonical BeDOM")
_expect_bedom_parent(html, "hidden", "template")
_expect_bedom_parent(html, "visible", "body")

step("Force template inertness after the authored CSS cascade")
expect(simple_web_layout_debug_style_by_id(
    html, "template", "display"
)).to_equal("none")
expect(simple_web_layout_debug_layout_by_id(
    html, 16, 8, "visible", "y"
)).to_equal("0")
val plan = browser_document_resource_plan(
    html, "https://safe.test/app", ""
)
expect(plan.script_blocks.len()).to_equal(0)
expect(plan.style_sources.len()).to_equal(1)
expect(plan.image_sources.len()).to_equal(0)

step("Omit inert commands and pixels from Draw IR execution")
val result = simple_web_layout_render_html_draw_ir_result(html, 16, 8)
expect(_has_command(result.composition, "hidden")).to_equal(false)
expect(_has_text(result.composition, "HIDDEN")).to_equal(false)
expect(_command_by_id(
    result.composition, "visible"
).parent_id).to_equal("body")
expect(_source_kind_for(
    result.composition, "visible"
)).to_equal("html_ast")
val pixels = _pixels(html, 16, 8)
expect(pixels[15]).to_equal(0xFF16A34Au32)
expect(pixels.contains(0xFFDC2626u32)).to_equal(false)
```

</details>

<details>
<summary>Advanced: should preserve component order and bounded projection caps</summary>

#### should preserve component order and bounded projection caps

- Keep legacy-stable generated component IDs after projection
- Respect the renderer node cap through canonical projection


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body><main style='width:8px;height:4px;" +
    "background:#dc2626'></main><aside style='width:8px;" +
    "height:4px;background:#2563eb'></aside></body></html>"
)

step("Keep legacy-stable generated component IDs after projection")
val result = simple_web_layout_render_html_draw_ir_result(html, 8, 8)
expect(_command_by_id(
    result.composition, "main_3"
).parent_id).to_equal("body_2")
expect(_command_by_id(
    result.composition, "aside_4"
).parent_id).to_equal("body_2")

step("Respect the renderer node cap through canonical projection")
expect(simple_web_layout_debug_capped_node_count(
    "<div><span>a</span><span>b</span></div>", 4
)).to_be_less_than(5)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
