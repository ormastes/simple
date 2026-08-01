# Canonical HTML Parsing Contexts

> This executable system specification proves that the canonical HTML tokenizer/tree builder feeds Web semantics, computed style, layout, `DrawIrComposition`, and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Canonical HTML Parsing Contexts

This executable system specification proves that the canonical HTML tokenizer/tree builder feeds Web semantics, computed style, layout, `DrawIrComposition`, and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/web_platform/html/html_parsing_contexts_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This executable system specification proves that the canonical HTML
tokenizer/tree builder feeds Web semantics, computed style, layout,
`DrawIrComposition`, and Engine2D.

It covers context-sensitive tree repair, inert template handling, generated
document structure, bounded projection, video poster rendering, and the safe
generic fallback used by embedded and media tags that do not yet have dedicated
resource execution.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md

**Requirements:** doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md

**Design:** N/A

**Research:** N/A

## Requirement Traceability

- `REQ-WEB-BROWSER-002` requires deterministic canonical HTML tree semantics.
- `REQ-WEB-BROWSER-003` requires bounded parsing and projection behavior.
- `REQ-WEB-BROWSER-004` requires Web output to lower through Draw IR and
  Engine2D rather than a private painter.

The embedded-media scenario also guards truthful fallback behavior for
`area`, `audio`, `canvas`, `embed`, `map`, `object`, `picture`, `source`,
`track`, and `video`.

`iframe` is deliberately excluded because its existing private `srcdoc`
renderer has a separate capability and security contract.

## Canonical Production Path

`html_tree_builder_build` constructs BeDOM.

The semantic checks use BeDOM paths, tags, node IDs, parent IDs, child order,
and text content. Source-text presence alone cannot satisfy those checks.

`simple_web_layout_render_html_draw_ir_result` projects the authored document
to Web semantic nodes, computed styles, layout boxes, and one
`DrawIrComposition`.

The composition source kind must remain `html_ast`.

`simple_web_layout_render_html_readback_engine2d_result` executes that
composition through Engine2D's software backend for exact pixel evidence.

No scenario uses the legacy HTML fallback painter or a private font path.

## Tree-Builder Scenarios

The paragraph scenario checks implied paragraph closure before a block sibling.

The foster-parent scenarios check element and text relocation around tables,
including exact source order and nested text retention.

The textarea scenario distinguishes an exact case-insensitive RCDATA closer
from a longer prefix that only resembles a closer.

The omitted-structure scenario independently checks generated `html` and
`body` elements while retaining stable component ancestry.

The template scenario keeps inert descendants in semantic state but excludes
their scripts, styles, images, layout, Draw IR, and pixels.

The bounded scenario checks stable generated component order and the selected
projection node cap.

## Embedded and Media Generic Fallback

One BeDOM build supplies all tag and parent assertions for the selected
embedded-media fixture.

Valid structural parents are retained:

- `area` remains inside `map`;
- `source` remains inside `picture`;
- `track` remains inside `video`.

The other selected tags remain children of `body`.

Authored `.fallback` CSS sets `display:block`, a 4 by 4 box, and a blue
background.

The renderer must not invent `display:none` for these generic elements.

Every selected element must retain the authored background, nonzero geometry,
and a component command in canonical Draw IR.

External-looking `href`, `src`, `srcset`, and `data` attributes are semantic
attributes only in this fallback profile. A `video` poster is deliberately
covered by the dedicated poster scenario below.

`browser_document_resource_plan` must report zero scripts, zero images, and
zero warnings while retaining the one authored inline stylesheet.

No selected Draw IR command may have kind `image` or a nonempty `image_uri`.

At least one exact blue pixel must reach the Engine2D readback.

This proves safe generic rendering; it does not claim media activation.

## Syntax

Run this source with the admitted pure-Simple test runtime:

```sh
bin/release/simple test test/03_system/feature/web_platform/html/html_parsing_contexts_spec.spl --mode=interpreter
```

The generated manual does not claim a runtime pass by itself.

Regenerate the mirrored manual with the repository's pure-Simple SPipe
document generator and the canonical `doc/06_spec` destination.

Executable `.spl` specifications remain under `test/`, never under
`doc/06_spec`.

## Examples

For `<p id='paragraph'><div id='after'>`, both elements become `body`
children and retain separate Draw IR boxes.

For table foster parenting, `FIRST`, the nested `span`, and `LAST` precede the
table in the repaired body child order.

For template inertness, hostile authored `display:block!important` cannot
activate the template subtree or its resource attributes.

For embedded media fallback, remote-looking attributes allocate no document
resource while authored blue boxes remain visible.

## Failure Interpretation

A missing tag, wrong parent, or wrong child order is a canonical tree failure.

A resource discovered under an inert template is a fail-open planning error.

A hidden generic embedded tag is an overbroad suppression error.

A media URL becoming a Draw IR image is an unauthorized resource escape; the
dedicated `video[poster]` image path is the only selected exception.

A correct semantic node without the expected layout or component command is a
Web projection failure.

A correct Draw IR composition without the discriminating pixel is an Engine2D
execution failure.

## Evidence Boundary

The specification proves the selected deterministic fixtures only.

It does not claim complete WHATWG parsing, media playback, Canvas scripting,
image candidate selection, image maps, plugin execution, native controls,
iframe security, or complete HTML/CSS conformance.

The posterless embedded-media fallback is intentionally resource-inactive.

Dedicated capabilities must add their own resource, security, lifecycle,
layout, Draw IR, and Engine2D evidence before promotion.

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

- Trace inert HTML through semantic state without Draw IR
   - Protocol capture: after_step
- path[path len
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
-  expect bedom parent
   - Protocol capture: after_step
- Force template inertness after the authored CSS cascade
   - Protocol capture: after_step
   - Evidence: protocol response verified by 5 expected checks
   - Expected: plan.script_blocks.len() equals `0`
   - Expected: plan.style_sources.len() equals `2`
   - Expected: plan.style_sources[0].source equals `/active.css`
   - Expected: plan.style_sources[1].source equals `template{display:block!important}#hidden{display:block!important}`
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

Runnable source: 90 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html id='document'><head id='head'>" +
    "<title id='title'>HIDDEN TITLE</title>" +
    "<base id='base' href='https://safe.test/'>" +
    "<meta id='meta' name='description' content='metadata'>" +
    "<link id='active-link' rel='stylesheet' href='/active.css'>" +
    "<style id='active-style'>template{display:block!important}" +
    "#hidden{display:block!important}</style>" +
    "</head><body id='body' style='margin:0'>" +
    "<template id='template' style='display:block!important'>" +
    "<script id='hidden-script' src='/hidden.js'></script>" +
    "<style>#visible{display:none!important}</style>" +
    "<link id='hidden-link' rel='stylesheet' href='/hidden.css'>" +
    "<img id='hidden-image' src='/hidden.png'>" +
    "<div id='hidden' style='display:block!important;width:16px;" +
    "height:8px;background:#dc2626'>HIDDEN</div></template>" +
    "<div id='visible' style='width:16px;height:8px;" +
    "background:#16a34a'></div></body></html>"
)

step("Trace inert HTML through semantic state without Draw IR")
val semantic_ids = [
    "head", "title", "base", "meta", "active-link", "active-style"
]
val semantic_tags = [
    "head", "title", "base", "meta", "link", "style"
]
val semantic_parents = [
    "document", "head", "head", "head", "head", "head"
]
var semantic_index = 0
while semantic_index < semantic_ids.len():
    _expect_bedom_parent(
        html, semantic_ids[semantic_index],
        semantic_parents[semantic_index]
    )
    val path = _path(html, semantic_ids[semantic_index])
    expect(be_dom_get_tag(
        path[path.len() - 1]
    )).to_equal(semantic_tags[semantic_index])
    expect(simple_web_layout_debug_layout_by_id(
        html, 16, 8, semantic_ids[semantic_index], "w"
    )).to_equal("")
    semantic_index = semantic_index + 1
_expect_bedom_parent(html, "hidden", "template")
_expect_bedom_parent(html, "visible", "body")

step("Force template inertness after the authored CSS cascade")
expect(simple_web_layout_debug_style_by_id(
    html, "template", "display"
)).to_equal("none")
expect([
    simple_web_layout_debug_layout_by_id(
        html, 16, 8, "template", "w"
    ),
    simple_web_layout_debug_layout_by_id(
        html, 16, 8, "template", "h"
    ),
    simple_web_layout_debug_layout_by_id(
        html, 16, 8, "hidden", "w"
    ),
    simple_web_layout_debug_layout_by_id(
        html, 16, 8, "hidden", "h"
    )
]).to_equal(["0", "0", "0", "0"])
expect(simple_web_layout_debug_layout_by_id(
    html, 16, 8, "visible", "y"
)).to_equal("0")
val plan = browser_document_resource_plan(
    html, "https://safe.test/app", ""
)
expect(plan.script_blocks.len()).to_equal(0)
expect(plan.style_sources.len()).to_equal(2)
expect(plan.style_sources[0].source).to_equal("/active.css")
expect(plan.style_sources[1].source).to_equal("template{display:block!important}#hidden{display:block!important}")
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

#### should preserve resource-safe generic fallback for embedded media tags

- Trace HTML elements through Web semantics and Draw IR
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 3 expected checks
   - Expected: be_dom_get_tag(node) equals `tags[index]`
   - Expected: node.parent_id equals `parent.node_id`
   - Expected: path[path.len() - 2].node_id equals `parent.node_id`
- Keep external media attributes out of document resource planning
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: plan.script_blocks.len() equals `0`
   - Expected: plan.style_sources.len() equals `1`
   - Expected: plan.image_sources.len() equals `0`
   - Expected: plan.warnings.len() equals `0`
- Preserve authored CSS through canonical Draw IR lowering
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: command.kind == "image" is false
   - Expected: command.image_uri equals ``
- Execute the generic fallback through Engine2D
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 88 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Trace HTML elements through Web semantics and Draw IR")
val html = (
    "<style>html,body{margin:0}.fallback{display:block;width:4px;" +
    "height:4px;background:#2563eb}</style><body id='body'>" +
    "<map id='map-row' class='fallback'>" +
    "<area id='area-row' class='fallback' " +
    "href='https://invalid.example/area'></map>" +
    "<audio id='audio-row' class='fallback' " +
    "src='https://invalid.example/audio'></audio>" +
    "<canvas id='canvas-row' class='fallback'></canvas>" +
    "<embed id='embed-row' class='fallback' " +
    "src='https://invalid.example/embed'>" +
    "<object id='object-row' class='fallback' " +
    "data='https://invalid.example/object'></object>" +
    "<picture id='picture-row' class='fallback'>" +
    "<source id='source-row' class='fallback' " +
    "srcset='https://invalid.example/picture 1x'></picture>" +
    "<video id='video-row' class='fallback' " +
    "src='https://invalid.example/video'>" +
    "<track id='track-row' class='fallback' " +
    "src='https://invalid.example/track'></video></body>"
)
val ids = [
    "area-row", "audio-row", "canvas-row", "embed-row", "map-row",
    "object-row", "picture-row", "source-row", "track-row", "video-row"
]
val tags = [
    "area", "audio", "canvas", "embed", "map",
    "object", "picture", "source", "track", "video"
]
val parents = [
    "map-row", "body", "body", "body", "body",
    "body", "body", "picture-row", "video-row", "body"
]

val root = html_tree_builder_build(html)
val identity_index = system_dom_identity_index(root)
var index = 0
while index < ids.len():
    val path = be_dom_path_for_route(
        root, identity_index, system_dom_route(identity_index, ids[index])
    )
    val parent_path = be_dom_path_for_route(
        root, identity_index,
        system_dom_route(identity_index, parents[index])
    )
    expect(path.len()).to_be_greater_than(1)
    expect(parent_path.len()).to_be_greater_than(0)
    val node = path[path.len() - 1]
    val parent = parent_path[parent_path.len() - 1]
    expect(be_dom_get_tag(node)).to_equal(tags[index])
    expect(node.parent_id).to_equal(parent.node_id)
    expect(path[path.len() - 2].node_id).to_equal(parent.node_id)
    index = index + 1

step("Keep external media attributes out of document resource planning")
val plan = browser_document_resource_plan(
    html, "https://safe.test/document", ""
)
expect(plan.script_blocks.len()).to_equal(0)
expect(plan.style_sources.len()).to_equal(1)
expect(plan.image_sources.len()).to_equal(0)
expect(plan.warnings.len()).to_equal(0)

step("Preserve authored CSS through canonical Draw IR lowering")
val result = simple_web_layout_render_html_draw_ir_result(
    html, 64, 64
)
index = 0
while index < ids.len():
    val node_index = _node_index(
        result.hit_index.nodes, ids[index]
    )
    expect(
        result.hit_index.styles[node_index].display == "none"
    ).to_equal(false)
    expect(result.hit_index.styles[node_index].bg).to_equal(
        0xFF2563EBu32
    )
    expect(result.hit_index.boxes.bw[node_index]).to_be_greater_than(0)
    expect(result.hit_index.boxes.bh[node_index]).to_be_greater_than(0)
    val command = _command_by_id(result.composition, ids[index])
    expect(command.kind == "image").to_equal(false)
    expect(command.image_uri).to_equal("")
    expect(_source_kind_for(
        result.composition, ids[index]
    )).to_equal("html_ast")
    index = index + 1

step("Execute the generic fallback through Engine2D")
expect(_pixels(
    html, 64, 64
).contains(0xFF2563EBu32)).to_equal(true)
```

</details>

#### should render an admitted video poster without fetching media

- Plan only the poster through the bounded image resource path
   - HTML capture: after_step
   - Expected: plan.image_sources.len() equals `1`
   - Expected: plan.image_sources[0].authored_src equals `/poster.png`
   - Expected: plan.image_sources[0].resolved_url equals `https://safe.test/poster.png`
- Bind the admitted poster to its video node
   - HTML capture: after_step
   - Expected: allowed.image_resources.len() equals `1`
   - Expected: allowed.admitted_image_sources.len() equals `1`
   - Expected: render HTML contains the admitted poster key while media URLs remain authored
- Lower the poster through canonical Draw IR and Engine2D
   - HTML capture: after_step
   - Expected: `stage_image` is an image command with the admitted resource key
   - Expected: the 4 by 4 Engine2D readback contains the poster color
- Block the same poster under img-src without painting an alias
   - HTML capture: after_step
   - Expected: blocked.image_resources.len() equals `0`
   - Expected: warnings contain the blocked poster URL
   - Expected: no `stage_image` command or poster-colored pixel survives


<details>
<summary>Executable SSpec</summary>

Runnable source: 79 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val poster_color = 0xFF14B8A6u32
val html = (
    "<html><head></head><body style='margin:0'>" +
    "<video id='stage' style='display:block;width:4px;height:4px' " +
    "poster='/poster.png' src='/movie.mp4'>" +
    "<source src='/movie.webm' type='video/webm'>" +
    "<track src='/captions.vtt' kind='captions'>" +
    "</video></body></html>"
)

step("Plan only the poster through the bounded image resource path")
val plan = browser_document_resource_plan(
    html, "https://safe.test/watch", ""
)
expect(plan.image_sources.len()).to_equal(1)
expect(plan.image_sources[0].authored_src).to_equal("/poster.png")
expect(plan.image_sources[0].resolved_url).to_equal(
    "https://safe.test/poster.png"
)

step("Bind the admitted poster to its video node")
var allowed = BrowserSession.new()
allowed.register_resource(
    "https://safe.test/poster.png", _poster_png_hex(poster_color)
)
expect(allowed.open_html(
    "https://safe.test/watch", html
).is_ok()).to_equal(true)
expect(allowed.image_resources.len()).to_equal(1)
expect(allowed.admitted_image_sources.len()).to_equal(1)
val render_html = allowed.render_html_document()
expect(render_html).to_contain(
    "poster=\"" + allowed.image_resources[0].image_uri + "\""
)
expect(render_html).to_contain("src=\"/movie.mp4\"")
expect(render_html).to_contain("src=\"/movie.webm\"")
expect(render_html).to_contain("src=\"/captions.vtt\"")

step("Lower the poster through canonical Draw IR and Engine2D")
val composition = simple_web_layout_render_html_draw_ir_with_images(
    render_html, 4, 4, allowed.image_resources
)
val command = _command_by_id(composition, "stage_image")
expect(command.kind).to_equal("image")
expect(command.image_uri).to_equal(
    allowed.image_resources[0].image_uri
)
val pixels = allowed.render_to_pixels(4, 4).pixel_data
expect(pixels.len()).to_equal(16)
expect(pixels.contains(poster_color)).to_equal(true)

step("Block the same poster under img-src without painting an alias")
var blocked = BrowserSession.new()
blocked.register_resource(
    "https://safe.test/poster.png", _poster_png_hex(poster_color)
)
expect(blocked.open_html(
    "https://safe.test/watch",
    "<html><head><meta http-equiv='content-security-policy' " +
    "content=\"img-src 'none'\"></head><body style='margin:0'>" +
    "<video id='stage' style='display:block;width:4px;height:4px' " +
    "poster='/poster.png'></video></body></html>"
).is_ok()).to_equal(true)
expect(blocked.image_resources.len()).to_equal(0)
expect(blocked.warnings.join("|")).to_contain(
    "CSP blocked image: https://safe.test/poster.png"
)
val blocked_composition =
    simple_web_layout_render_html_draw_ir_with_images(
        blocked.render_html_document(), 4, 4,
        blocked.image_resources
    )
expect(_has_command(
    blocked_composition, "stage_image"
)).to_equal(false)
expect(blocked.render_to_pixels(
    4, 4
).pixel_data.contains(poster_color)).to_equal(false)

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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/html_css_spec_traceability.md`


</details>
