# office_suite_spec

> Exercises the canonical Office app entrypoint, launcher, headless action dispatcher, and app-specific UI construction paths. The suite verifies Markdown-backed Writer, Calc, Impress, Draw/SDD, Designer, Base, Math, Counter, Mail, and Planner stay reachable through the shared LibreOffice-like shell.

<!-- sdn-diagram:id=office_suite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=office_suite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

office_suite_spec -> std
office_suite_spec -> app
office_suite_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=office_suite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 168 | 168 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_suite_spec

Exercises the canonical Office app entrypoint, launcher, headless action dispatcher, and app-specific UI construction paths. The suite verifies Markdown-backed Writer, Calc, Impress, Draw/SDD, Designer, Base, Math, Counter, Mail, and Planner stay reachable through the shared LibreOffice-like shell.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/ide_office_plugin_suite.md |
| Design | doc/07_guide/app/ide_office_plugin_suite.md |
| Research | N/A |
| Source | `test/01_unit/app/office/office_suite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the canonical Office app entrypoint, launcher, headless action
dispatcher, and app-specific UI construction paths. The suite verifies
Markdown-backed Writer, Calc, Impress, Draw/SDD, Designer, Base, Math, Counter,
Mail, and Planner stay reachable through the shared LibreOffice-like shell.

## Examples

`run_office(["writer"])` loads the Markdown-backed Writer surface.
`office_action_dispatch("render-writer-markdown-html", source)` renders the
HTML document path. `office_catalog_dispatch_probe()` verifies every
LLM-catalog action is recognized through plugin-context dispatch with catalog
component, source-format, and evidence metadata.

**Requirements:** N/A
**Plan:** doc/03_plan/sys_test/ide_office_plugin_suite.md
**Design:** doc/07_guide/app/ide_office_plugin_suite.md
**Research:** N/A

## Scenarios

### Office CLI

#### defaults to launcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office([])).to_equal(0)
```

</details>

#### loads word

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["word"])).to_equal(0)
```

</details>

#### loads writer as the markdown-backed word processor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["writer"])).to_equal(0)
```

</details>

#### loads sheets

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheets"])).to_equal(0)
```

</details>

#### loads calc aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["calc"])).to_equal(0)
expect(run_office(["excel"])).to_equal(0)
```

</details>

#### loads slides

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slides"])).to_equal(0)
```

</details>

#### loads impress aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["impress"])).to_equal(0)
expect(run_office(["ppt"])).to_equal(0)
```

</details>

#### loads draw base and math direct routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["draw"])).to_equal(0)
expect(run_office(["base"])).to_equal(0)
expect(run_office(["db"])).to_equal(0)
expect(run_office(["math"])).to_equal(0)
```

</details>

#### loads mail

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["mail"])).to_equal(0)
```

</details>

#### loads planner

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["planner"])).to_equal(0)
```

</details>

#### loads counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["counter"])).to_equal(0)
```

</details>

#### loads apps through launcher open actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["open_word"])).to_equal(0)
expect(run_office(["open_sheets"])).to_equal(0)
expect(run_office(["open_slides"])).to_equal(0)
expect(run_office(["open_draw"])).to_equal(0)
expect(run_office(["open_db"])).to_equal(0)
expect(run_office(["open_math"])).to_equal(0)
expect(run_office(["open_mail"])).to_equal(0)
expect(run_office(["open_planner"])).to_equal(0)
expect(run_office(["open_counter"])).to_equal(0)
```

</details>

#### applies markdown edit commands when expected source matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["md-edit", "1", "second", "changed", "first\\nsecond"])).to_equal(0)
```

</details>

#### rejects markdown edit commands when actual source differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["md-edit", "1", "expected", "changed", "first\\nactual"])).to_equal(2)
```

</details>

#### rejects markdown edit commands with trailing arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["md-edit", "1", "second", "changed", "first\\nsecond", "extra"])).to_equal(1)
```

</details>

#### rejects markdown edit commands with malformed line tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["md-edit", "abc", "first", "changed", "first\\nsecond"])).to_equal(2)
expect(run_office(["md-edit", "-1", "first", "changed", "first\\nsecond"])).to_equal(2)
expect(run_office(["md-edit", "", "first", "changed", "first\\nsecond"])).to_equal(2)
expect(run_office(["md-edit", "9999999999", "first", "changed", "first\\nsecond"])).to_equal(2)
```

</details>

#### applies sheet edit commands when expected cell display matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1=old;B1=2"])).to_equal(0)
expect(run_office(["sheet-edit", "A1", "old;semi", "new", "A1=old\\;semi;B1=2"])).to_equal(0)
```

</details>

#### rejects sheet edit commands when actual cell display differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "expected", "new", "A1=actual;B1=2"])).to_equal(2)
```

</details>

#### rejects sheet edit commands with malformed target references

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "not-a-ref", "", "new", "A1=old"])).to_equal(2)
```

</details>

#### rejects sheet edit commands with blank target refs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "   ", "old", "new", "A1=old"])).to_equal(2)
```

</details>

#### rejects sheet edit commands for missing target cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "", "new", ""])).to_equal(2)
```

</details>

#### rejects sheet edit commands with malformed source entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1old;B1=2"])).to_equal(2)
```

</details>

#### rejects sheet edit commands with malformed source references

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1=old;not-a-ref=2"])).to_equal(2)
```

</details>

#### rejects sheet edit commands with duplicate source references

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1=old;A01=new"])).to_equal(2)
```

</details>

#### rejects sheet edit commands with trailing arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1=old", "extra"])).to_equal(1)
```

</details>

#### applies slide edit commands when expected text matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "title=old;body=second"])).to_equal(0)
expect(run_office(["slide-edit", "title", "old;semi", "new", "title=old\\;semi;body=second"])).to_equal(0)
```

</details>

#### rejects slide edit commands when actual text differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "expected", "new", "title=actual;body=second"])).to_equal(2)
```

</details>

#### rejects slide edit commands for missing elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "", "new", "body=second"])).to_equal(2)
```

</details>

#### rejects slide edit commands with blank target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "   ", "old", "new", "title=old"])).to_equal(2)
```

</details>

#### rejects slide edit commands with malformed source entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "titleold;body=second"])).to_equal(2)
```

</details>

#### rejects slide edit commands with missing source ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "=old"])).to_equal(2)
```

</details>

#### rejects slide edit commands with duplicate source ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "title=old;title=new"])).to_equal(2)
```

</details>

#### rejects slide edit commands with trailing arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "title=old", "extra"])).to_equal(1)
```

</details>

#### rejects unknown app

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["unknown"])).to_equal(1)
```

</details>

#### dispatches Writer Markdown HTML rendering as a headless office action

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-writer-markdown-html", "# Title\\n\\nBody")
expect(result.ok).to_be(true)
expect(result.code).to_equal(0)
expect(result.output).to_contain("class=\"md-paper\"")
expect(result.output).to_contain("data-format=\"markdown-paper\"")
expect(result.output).to_contain("data-format-name=\"Writer Markdown\"")
expect(result.output).to_contain("Title")
```

</details>

#### dispatches through an explicit plugin context

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = office_plugin_context("render-writer-markdown-html", "writer", "markdown", "word/html_render_spec")
val result = office_action_dispatch_with_context(context, "# Title")
val invalid = office_action_dispatch_with_context(office_plugin_context("   ", "writer", "markdown", "word/html_render_spec"), "# Title")
val mismatched = office_action_dispatch_with_context(office_plugin_context("render-writer-markdown-html", "slides", "markdown", "word/html_render_spec"), "# Title")
val wrong_format = office_action_dispatch_with_context(office_plugin_context("render-writer-markdown-html", "writer", "sdd", "word/html_render_spec"), "# Title")
expect(result.ok).to_be(true)
expect(result.output).to_contain("data-format-name=\"Writer Markdown\"")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-context")
expect(mismatched.ok).to_be(false)
expect(mismatched.reason).to_equal("context-mismatch")
expect(wrong_format.ok).to_be(false)
expect(wrong_format.reason).to_equal("source-format-mismatch")
```

</details>

#### summarizes Writer as a Markdown-backed document surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-summary", "# Title\\n\\nBody")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("summarized")
expect(result.output).to_contain("source=markdown")
expect(result.output).to_contain("format=Writer Markdown")
expect(result.output).to_contain("lines=3")
expect(result.output).to_contain("render=html")
```

</details>

#### counts Writer Markdown document statistics

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-stats", "# Title\\n\\nBody words\\n\\n## Next\\n```\\n# hidden\\n```")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("counted")
expect(result.output).to_equal("lines=8\nblocks=3\nheadings=2\nwords=6")
```

</details>

#### searches Writer Markdown source by line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-search", "draft\n# Title\nfirst draft\nsecond")
val invalid = office_action_dispatch("writer-markdown-search", "   \n# Title")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("listed")
expect(result.output).to_equal("1|6|first draft")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
```

</details>

#### reads Writer Markdown source ranges with line numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-range", "1|2\n# Title\nFirst\nSecond\nThird")
val invalid = office_action_dispatch("writer-markdown-range", "9|1\n# Title")
val extra = office_action_dispatch("writer-markdown-range", "1|2|ignored\n# Title\nFirst\nSecond")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("listed")
expect(result.output).to_equal("1|First\n2|Second")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
expect(extra.ok).to_be(false)
expect(extra.reason).to_equal("invalid-args")
```

</details>

#### lists Writer Markdown blocks with source line anchors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-blocks", "# Title\n\nBody\n- Item")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("listed")
expect(result.output).to_equal("0|0|0|heading|# Title\n1|2|2|paragraph|Body\n2|3|3|list|- Item")
```

</details>

#### lists Writer Markdown table rows with source line anchors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-tables", "# Title\n| A | B |\n|---|---|\n| 1 | 2 |")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("listed")
expect(result.output).to_equal("0|1|1|\\| A \\| B \\|\n1|2|2|\\|---\\|---\\|\n2|3|3|\\| 1 \\| 2 \\|")
```

</details>

#### replaces Writer Markdown source text

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-replace", "draft|final\n# Title\nfirst draft\nsecond draft")
val invalid = office_action_dispatch("writer-markdown-replace", "   |final\n# Title")
val extra = office_action_dispatch("writer-markdown-replace", "draft|final|ignored\n# Title\nfirst draft")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.output).to_equal("# Title\nfirst final\nsecond final")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
expect(extra.ok).to_be(false)
expect(extra.reason).to_equal("invalid-args")
```

</details>

#### inserts Writer Markdown source lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-insert", "1|## Added\n# Title\nBody")
val invalid = office_action_dispatch("writer-markdown-insert", "9|Late\n# Title")
val extra = office_action_dispatch("writer-markdown-insert", "1|## Added|ignored\n# Title\nBody")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.output).to_equal("# Title\n## Added\nBody")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
expect(extra.ok).to_be(false)
expect(extra.reason).to_equal("invalid-args")
```

</details>

#### deletes Writer Markdown source lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-delete", "1\n# Title\nRemove me\nBody")
val invalid = office_action_dispatch("writer-markdown-delete", "9\n# Title")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.output).to_equal("# Title\nBody")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
```

</details>

#### lists Writer Markdown headings as a document outline

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("writer-markdown-outline", "# Title\\n\\n## Section\\n```\\n# hidden\\n```\\n### Detail")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("listed")
expect(result.output).to_equal("0|1|Title\n2|2|Section\n6|3|Detail")
```

</details>

#### dispatches PPT Markdown HTML rendering as a headless office action

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-ppt-markdown-html", "# Deck\\n\\n## Slide\\nBody")
expect(result.ok).to_be(true)
expect(result.output).to_contain("class=\"md-ppt-deck\"")
expect(result.output).to_contain("data-format=\"markdown-ppt\"")
expect(result.output).to_contain("Slide")
```

</details>

#### lists PPT Markdown slides as an Impress outline

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ppt-markdown-outline", "# Deck\\n\\n## Intro\\nBody\\n```\\n## Hidden\\n```\\n## Roadmap")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("listed")
expect(result.output).to_equal("1|2|Intro\n2|7|Roadmap")
```

</details>

#### dispatches UI render and SDD export catalog actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "design: Feature\\nsize: 640x480\\nnode button|Run|button|16|20|96|32|primary|controls|action"
val html = office_action_dispatch("render-ui-html", source)
val selected_html = office_action_dispatch("render-ui-html-with-selection", "select|button\\n" + source)
val invalid_selected_html = office_action_dispatch("render-ui-html-with-selection", "select|button bad\\n" + source)
val sdd = office_action_dispatch("export-ui-sdd", source)
val style_tokens = office_action_dispatch("ui-style-tokens-read", source)
val legacy_html = office_action_dispatch("ui-render", source)
val legacy_sdd = office_action_dispatch("ui-export-sdd", source)
expect(html.ok).to_be(true)
expect(html.output).to_contain("data-format=\"html-ui\"")
expect(html.output).to_contain("data-node-count=\"1\"")
expect(html.output).to_contain("Run")
expect(selected_html.ok).to_be(true)
expect(selected_html.output).to_contain("data-selected-node-id=\"button\"")
expect(selected_html.output).to_contain("data-selected=\"true\"")
expect(selected_html.output).to_contain("data-resize-handle=\"se\"")
expect(invalid_selected_html.ok).to_be(false)
expect(invalid_selected_html.reason).to_equal("invalid-args")
expect(sdd.ok).to_be(true)
expect(sdd.output).to_contain("graph: Feature")
expect(sdd.output).to_contain("nodes |id, label, css, role, shape, x, y, width, height, layer, parent")
expect(style_tokens.output).to_equal("nodes=1\nbutton=primary")
expect(legacy_html.action).to_equal("render-ui-html")
expect(legacy_html.output).to_contain("data-format=\"html-ui\"")
expect(legacy_sdd.action).to_equal("export-ui-sdd")
expect(legacy_sdd.output).to_contain("graph: Feature")
```

</details>

#### dispatches selected SDD HTML rendering from the Draw catalog action

<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-sdd-html-with-selection", "graph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val summary = office_action_dispatch("sdd-document-summary", "graph: Feature\\ncanvas: width: 640 height: 480 grid: 16 snap: true zoom: 100 background: white\\ncss accent:\\n    fill: #eeeeee\\nA: Alpha @accent x: 0 y: 0 width: 80 height: 20\\nB: Beta x: 120 y: 0 width: 80 height: 20\\nA -> B: Link")
val outline = office_action_dispatch("sdd-outline-read", "graph: Feature\\nA: Alpha|Ready role: actor shape: diamond\\nB: Beta parent: A\\nA -> B: Link|Flow kind: async")
val style_rules = office_action_dispatch("sdd-style-rules-read", "graph: Feature\\ncss base:\\n    stroke: #111111\\ncss accent extends base target edge:\\n    fill: #eeeeee")
val weave = office_action_dispatch("sdd-weave-summary", "graph: Weave\\nweave @:\\n    node where role=actor:\\n        add: accent\\n        shape: diamond\\n        x: 10\\n        y: 20\\n        layer: front\\n    edge where kind=async:\\n        add: dashed\\nA: Alpha role: actor\\nB: Beta\\nA -> B: link kind: async")
val selected = office_action_dispatch("render-sdd-html-with-selection", "select|A|\\ngraph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val selected_edge = office_action_dispatch("render-sdd-html-with-selection", "select||0\\ngraph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20\\nB: Beta x: 120 y: 0 width: 80 height: 20\\nA -> B: Link route: orthogonal waypoints: 80x10 start: right end: left")
val canonical = office_action_dispatch("export-sdd-canonical", "graph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val invalid = office_action_dispatch("render-sdd-html-with-selection", "select|A bad|\\ngraph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val legacy = office_action_dispatch("render-sdd", "graph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
expect(result.ok).to_be(true)
expect(result.output).to_contain("class=\"sdn-graph sdd-diagram\"")
expect(result.output).to_contain("data-node=\"A\"")
expect(result.output).to_contain("data-node-index=\"0\"")
expect(result.output).to_contain("data-label=\"Alpha\"")
expect(result.output).to_contain("data-selected-node-id=\"\"")
expect(result.output).to_contain("data-selected-edge-index=\"-1\"")
expect(summary.ok).to_be(true)
expect(summary.reason).to_equal("summarized")
expect(summary.output).to_equal("name=Feature\nnodes=2\nedges=1\ncss_rules=1\nstyle_rows=1\ncanvas=true")
expect(outline.ok).to_be(true)
expect(outline.output).to_contain("node 0:A|Alpha\\|Ready|actor|diamond|")
expect(outline.output).to_contain("node 1:B|Beta|||A")
expect(outline.output).to_contain("edge 0:A->B|Link\\|Flow|async")
expect(style_rules.output).to_contain("css_rules=2")
expect(style_rules.output).to_contain("css accent extends=base target=edge")
expect(style_rules.output).to_contain("style accent.fill=#eeeeee")
expect(weave.ok).to_be(true)
expect(weave.output).to_contain("weaves=2")
expect(weave.output).to_contain("0:target=node field=role value=actor add=accent shape=diamond x=10 y=20")
expect(weave.output).to_contain("1:target=edge field=kind value=async add=dashed")
expect(selected.ok).to_be(true)
expect(selected.output).to_contain("data-selected-node-id=\"A\"")
expect(selected.output).to_contain("data-selected=\"true\"")
expect(selected.output).to_contain("data-resize-handle=\"se\" data-node=\"A\" data-node-index=\"0\"")
expect(selected_edge.output).to_contain("data-connector-handle=\"start\" data-edit-action=\"reconnect-start\" data-handle-index=\"0\" data-edge-index=\"0\" data-label=\"Link\" data-kind=\"\" data-route=\"orthogonal\" data-anchor=\"right\" data-x=\"80\" data-y=\"10\"")
expect(selected_edge.output).to_contain("data-connector-handle=\"end\" data-edit-action=\"reconnect-end\" data-handle-index=\"1\" data-edge-index=\"0\" data-label=\"Link\" data-kind=\"\" data-route=\"orthogonal\" data-anchor=\"left\"")
expect(selected_edge.output).to_contain("data-connector-handle=\"label\" data-edit-action=\"move-label\" data-handle-index=\"2\"")
expect(selected_edge.output).to_contain("data-connector-handle=\"waypoint\" data-edit-action=\"move-waypoint\" data-handle-index=\"3\" data-waypoint-index=\"0\" data-edge-index=\"0\" data-label=\"Link\" data-kind=\"\" data-route=\"orthogonal\" data-x=\"80\" data-y=\"10\"")
expect(selected_edge.output).to_contain("data-y=\"10\" data-from=\"A\" data-to=\"B\"")
expect(selected_edge.output).to_contain("data-from=\"A\" data-to=\"B\" data-node=\"A\"")
expect(selected_edge.output).to_contain("data-from=\"A\" data-to=\"B\" data-node=\"B\"")
expect(selected_edge.output).to_contain("data-node=\"A\" data-opposite-node=\"B\"")
expect(selected_edge.output).to_contain("data-node=\"B\" data-opposite-node=\"A\"")
expect(selected_edge.output).to_contain("data-start-anchor=\"right\" data-end-anchor=\"left\"")
expect(selected_edge.output).to_contain("data-from=\"A\" data-to=\"B\" data-start-anchor=\"right\" data-end-anchor=\"left\"")
expect(canonical.output).to_contain("nodes |id, label, css, role, shape, x, y, width, height, layer, parent|")
expect(canonical.output).to_contain("    A, Alpha")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
expect(legacy.action).to_equal("render-sdd-html")
expect(legacy.output).to_contain("class=\"sdn-graph sdd-diagram\"")
```

</details>

#### rejects malformed Base table HTML rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-base-table-html", "table: Bad\\ncolumns: id,status\\nrow: 1")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("row-width-mismatch")
```

</details>

#### renders Base table HTML with escaped cell coordinates

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-base-table-html", "table: Feature\\ncolumns: id,status\\nrow: 1,<open>")
val quoted = office_action_dispatch("render-base-table-html", "table: Feature\\ncolumns: id,status\\nrow: 1,\"open,ready\"")
expect(result.ok).to_be(true)
expect(result.output).to_contain("data-format-name=\"Base Table\"")
expect(result.output).to_contain("scope=\"col\" data-column=\"status\"")
expect(result.output).to_contain("<tr data-row-index=\"0\">")
expect(result.output).to_contain("<td data-row-index=\"0\" data-column=\"status\">&lt;open&gt;</td>")
expect(quoted.ok).to_be(true)
expect(quoted.output).to_contain("<td data-row-index=\"0\" data-column=\"status\">open,ready</td>")
```

</details>

#### summarizes Base table schema and row count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("base-table-summary", "table: Feature\ncolumns: id,status\nrow: 1,open\nrow: 2,done")
val invalid = office_action_dispatch("base-table-summary", "table: Feature\ncolumns: id,status\nrow: 1")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("summarized")
expect(result.output).to_equal("table=Feature\ncolumns=id,status\nrows=2")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("row-width-mismatch")
```

</details>

#### rejects malformed Base table queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("query-table", "count-where|status|open\\ntable: Bad\\ncolumns: id,status\\nrow: 1")
val malformed_quote = office_action_dispatch("render-base-table-html", "table: Bad\\ncolumns: id,status\\nrow: 1,\"open")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("row-width-mismatch")
expect(malformed_quote.ok).to_be(false)
expect(malformed_quote.reason).to_equal("row-width-mismatch")
```

</details>

#### rejects duplicate Base table columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("db-edit", "insert|2,done,done\\ntable: Bad\\ncolumns: id,status,status\\nrow: 1,open,open")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("duplicate-column")
```

</details>

#### preserves quoted comma Base cells through edits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("db-edit", "insert|2,\"done,ready\"\\ntable: Feature\\ncolumns: id,status\\nrow: 1,\"open,ready\"")
expect(result.ok).to_be(true)
expect(result.output).to_contain("row: 1,\"open,ready\"")
expect(result.output).to_contain("row: 2,\"done,ready\"")
```

</details>

#### preserves escaped pipe Base action values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = office_action_dispatch("db-edit", "insert|2,open\\|closed\\ntable: Feature\\ncolumns: id,status\\nrow: 1,open")
val query = office_action_dispatch("query-table", "count-where|status|open\\|closed\\ntable: Feature\\ncolumns: id,status\\nrow: 1,open|closed")
expect(edit.ok).to_be(true)
expect(edit.output).to_contain("row: 2,open|closed")
expect(query.ok).to_be(true)
expect(query.output).to_equal("1")
```

</details>

#### preserves escaped pipe document edit action values

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val replace = office_action_dispatch("writer-markdown-replace", "draft\\|old|draft\\|new\n# Title\nfirst draft|old")
val insert = office_action_dispatch("writer-markdown-insert", "1|added\\|line\n# Title\nBody")
val markdown = office_action_dispatch("md-edit", "1|old\\|value|new\\|value\n# Title\nold|value")
val sheet = office_action_dispatch("sheet-edit", "A1|old\\|value|new\\|value\nA1=old|value")
val slide = office_action_dispatch("slide-edit", "title|old\\|value|new\\|value\ntitle=old|value")
expect(replace.ok).to_be(true)
expect(replace.output).to_contain("draft|new")
expect(insert.ok).to_be(true)
expect(insert.output).to_contain("added|line")
expect(markdown.ok).to_be(true)
expect(markdown.output).to_contain("new|value")
expect(sheet.ok).to_be(true)
expect(sheet.output).to_equal("A1=new|value")
expect(slide.ok).to_be(true)
expect(slide.output).to_equal("title=new|value")
```

</details>

#### rejects blank Base table columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("db-edit", "insert|2,done,done\\ntable: Bad\\ncolumns: id,,status\\nrow: 1,open,open")
val malformed_quote = office_action_dispatch("base-table-summary", "table: Bad\\ncolumns: id,\"status\\nrow: 1,open")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("blank-column")
expect(malformed_quote.ok).to_be(false)
expect(malformed_quote.reason).to_equal("missing-columns")
```

</details>

#### rejects blank Base table names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-base-table-html", "table: \\ncolumns: id,status\\nrow: 1,open")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("missing-table-name")
```

</details>

#### rejects blank Base query columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("query-table", "count-where|   |open\ntable: Feature\ncolumns: id,status\nrow: 1,open")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank Base edit columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val update_result = office_action_dispatch("db-edit", "update-where|   |open|status|done\ntable: Feature\ncolumns: id,status\nrow: 1,open")
val delete_result = office_action_dispatch("db-edit", "delete-where|   |open\ntable: Feature\ncolumns: id,status\nrow: 1,open")
val missing_result = office_action_dispatch("db-edit", "update-where|missing|open|status|done\ntable: Feature\ncolumns: id,status\nrow: 1,open")
expect(update_result.ok).to_be(false)
expect(update_result.reason).to_equal("invalid-args")
expect(delete_result.ok).to_be(false)
expect(delete_result.reason).to_equal("invalid-args")
expect(missing_result.reason).to_equal("missing-match-column")
```

</details>

#### rejects unknown headless office actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("unknown-action", "")
expect(result.ok).to_be(false)
expect(result.code).to_equal(1)
expect(result.reason).to_equal("unknown-action")
```

</details>

#### rejects blank counter action names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("counter-action", "5|   ")
val escaped = office_action_dispatch("counter-action", "5|counter\\|increment")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
expect(escaped.ok).to_be(false)
expect(escaped.reason).to_equal("unsupported")
```

</details>

#### formats Calc numeric display values

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val currency = office_action_dispatch("format-cell-value", "1234.5|currency:$:2")
val escaped = office_action_dispatch("format-cell-value", "1234.5|currency:\\|:0")
val percent = office_action_dispatch("format-cell-value", "0.375|percent:1")
val invalid = office_action_dispatch("format-cell-value", "12x|number:2")
expect(currency.output).to_equal("$1,234.50")
expect(currency.reason).to_equal("formatted")
expect(escaped.output).to_equal("|1,235")
expect(escaped.reason).to_equal("formatted")
expect(percent.output).to_equal("37.5%")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
```

</details>

#### evaluates Calc formulas as read-only display values

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = office_action_dispatch("evaluate-sheet-formula", "=A1+B1\nA1=2;B1=3")
val counta = office_action_dispatch("evaluate-sheet-formula", "COUNTA(A1:B1)\nA1=2;B1=text")
val invalid = office_action_dispatch("evaluate-sheet-formula", "   \nA1=2")
expect(sum.output).to_equal("5")
expect(sum.reason).to_equal("evaluated")
expect(counta.output).to_equal("2")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
```

</details>

#### dispatches Designer resolved auto-layout readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-resolved-layout-read", "design: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container||vertical|8|4,4,4,4\nnode button|Run|button|16|16|80|32|primary|2|action|frame")
expect(result.ok).to_be(true)
expect(result.reason).to_equal("listed")
expect(result.output).to_contain("data-node=\"button\"")
expect(result.output).to_contain("left: 4px")
expect(result.output).to_contain("top: 4px")
```

</details>

#### recognizes every LLM catalog office action

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = office_catalog_dispatch_probe()
expect(probe.advertised_count).to_equal(137)
expect(probe.recognized_count).to_equal(137)
expect(probe.missing_actions.len()).to_equal(0)
```

</details>

#### publishes source formats in the LLM catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = ""
for row in office_llm_feature_catalog():
    formats = formats + row.component + ":" + row.source_format + "\n"
expect(formats).to_contain("word:markdown")
expect(formats).to_contain("slides:slides")
expect(formats).to_contain("draw:sdd")
expect(formats).to_contain("ui:html-ui")
expect(formats).to_contain("db:table")
expect(formats).to_contain("launcher:launcher")
```

</details>

#### rejects unsupported LLM catalog source formats

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_rows = [OfficeLlmFeature(
    app_name: "Bad",
    component: "bad",
    source_format: "binary",
    owner_module: "app.office.bad",
    features: ["feature"],
    actions: ["bad-action"],
    evidence_key: "bad_spec"
)]
expect(office_llm_catalog_validate(bad_rows)).to_contain("invalid source format")
```

</details>

### Office UI

#### builds launcher ui

- RecentFile
   - Expected: ui.root_id equals `root`
   - Expected: ui.title_text() equals `LibreOffice`
   - Expected: launcher_app_cards().len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recent = [
    RecentFile(path: "/tmp/test.sdoc", app_name: "word", title: "Test Doc", timestamp: "2026-03-25")
]
val ui = build_launcher_ui(recent)
expect(ui.root_id).to_equal("root")
expect(ui.title_text()).to_equal("LibreOffice")
expect(launcher_app_cards().len()).to_equal(9)
```

</details>

#### keeps launcher actions allowlisted and resolves counter actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(launcher_action_allowlist().len()).to_equal(9)
expect(launcher_open_action("word")).to_equal("open_word")
expect(is_valid_launcher_action("open_word")).to_be(true)
expect(is_valid_launcher_action("open_draw")).to_be(true)
expect(is_valid_launcher_action("open_db")).to_be(true)
expect(is_valid_launcher_action("open_math")).to_be(true)
expect(is_valid_launcher_action("open_mail")).to_be(true)
expect(is_valid_launcher_action("open_planner")).to_be(true)
expect(is_valid_launcher_action("open_counter")).to_be(true)
val slides = launcher_action_to_component("open_slides")
expect(slides.is_some()).to_be(true)
expect(slides.unwrap()).to_equal("slides")
val draw = launcher_action_to_component("open_draw")
expect(draw.is_some()).to_be(true)
expect(draw.unwrap()).to_equal("draw")
val mail = launcher_action_to_component("open_mail")
expect(mail.is_some()).to_be(true)
expect(mail.unwrap()).to_equal("mail")
val planner = launcher_action_to_component("open_planner")
expect(planner.is_some()).to_be(true)
expect(planner.unwrap()).to_equal("planner")
val counter = launcher_action_to_component("open_counter")
expect(counter.is_some()).to_be(true)
expect(counter.unwrap()).to_equal("counter")
```

</details>

#### builds word ui

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = WordApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("word_root")
expect(app.word_count()).to_equal(0)
```

</details>

#### builds sheets ui

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = SheetsApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
```

</details>

#### caches display-safe Calc formulas through app edit confirmation

- var app = SheetsApp new
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- app navigate to
- app formula text = "=COUNTA
- app confirm edit
   - Expected: cell_display_text(app.workbook.active().get_cell("C1")) equals `5`
- app navigate to
- app formula text = "=VLOOKUP
- app confirm edit
   - Expected: cell_display_text(app.workbook.active().get_cell("C2")) equals `2`
- app navigate to
- app formula text = "=TRIM
- app confirm edit
   - Expected: cell_display_text(app.workbook.active().get_cell("C3")) equals `Mixed Case`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = SheetsApp.new()
val sheet = app.workbook.active()
sheet.set_value("A1", "Alpha")
sheet.set_value("A2", "")
sheet.set_value("A3", "42")
sheet.set_value("A4", "=LEN(\"xy\")")
sheet.set_value("B1", "FALSE")
sheet.set_value("D1", "A-1")
sheet.set_value("A6", "A-1")
sheet.set_value("B6", "Bolt")
sheet.set_value("C6", "=LEN(\"xx\")")
sheet.set_value("A7", "B-2")
sheet.set_value("B7", "Nut")
sheet.set_value("C7", "9")
app.workbook.sheets = [sheet]

app.navigate_to(2, 0)
app.formula_text = "=COUNTA(A1:A4,B1,\"x\",\"\")"
app.confirm_edit()
expect(cell_display_text(app.workbook.active().get_cell("C1"))).to_equal("5")

app.navigate_to(2, 1)
app.formula_text = "=VLOOKUP(D1,A6:C7,3,FALSE)"
app.confirm_edit()
expect(cell_display_text(app.workbook.active().get_cell("C2"))).to_equal("2")

app.navigate_to(2, 2)
app.formula_text = "=TRIM(\"  Mixed Case  \")"
app.confirm_edit()
expect(cell_display_text(app.workbook.active().get_cell("C3"))).to_equal("Mixed Case")
```

</details>

#### builds slides ui

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = SlidesApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
```

</details>

#### builds mail ui with sample data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = MailApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
expect(app.emails.len()).to_equal(5)
expect(app.unread_count()).to_equal(2)
```

</details>

#### builds planner ui

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = PlannerApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
```

</details>

#### builds counter ui and applies deterministic transitions

- var app = CounterApp new
   - Expected: ui.root_id equals `root`
   - Expected: inc.value equals `1`
   - Expected: inc.status equals `incremented`
- app handle event
   - Expected: app.value equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = CounterApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
val inc = counter_apply_action(app.value, "counter_increment")
expect(inc.value).to_equal(1)
expect(inc.status).to_equal("incremented")
app.handle_event(UIEvent.Action(name: "counter_increment"))
expect(app.value).to_equal(1)
```

</details>

### Office Hardening

#### adds slides image element without fake asset path

- var app = SlidesApp new
- app handle event
   - Expected: slide.elements.len() equals `2`
- SlideElementKind ImageEl
   - Expected: image_src equals ``
   - Expected: image_alt equals `Image Frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = SlidesApp.new()
app.handle_event(UIEvent.Action(name: "add_image"))
val slide = current_slide(app.presentation)
expect(slide.elements.len()).to_equal(2)
var image_src = "<not-image>"
var image_alt = "<not-image>"
match slide.elements[slide.elements.len() - 1].kind:
    SlideElementKind.ImageEl(src: src, alt: alt):
        image_src = src
        image_alt = alt
    _:
        image_src = "<not-image>"
        image_alt = "<not-image>"
expect(image_src).to_equal("")
expect(image_alt).to_equal("Image Frame")
```

</details>

#### formats date values honestly in sheets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val formatted = apply_cell_format(366.0, "date")
expect(formatted).to_equal("1971-01-02")
```

</details>

#### updates sheets cells only when expected display matches

- sheet set value
   - Expected: result.reason equals `updated`
   - Expected: result.diff equals `@@ cell A1 @@\n- old\n+ new`
   - Expected: cell_display_text(sheet.get_cell("A1")) equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Checked")
sheet.set_value("A1", "old")
val result = sheet.update_cell_checked("A1", "old", "new")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.diff).to_equal("@@ cell A1 @@\n- old\n+ new")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("new")
```

</details>

#### rejects stale sheet cell updates without mutating

- sheet set value
   - Expected: result.reason equals `stale-cell`
   - Expected: result.diff equals `@@ cell A1 @@\nexpected: expected\nactual: actual\nrejected: new`
   - Expected: cell_display_text(sheet.get_cell("A1")) equals `actual`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Checked")
sheet.set_value("A1", "actual")
val result = sheet.update_cell_checked("A1", "expected", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("stale-cell")
expect(result.diff).to_equal("@@ cell A1 @@\nexpected: expected\nactual: actual\nrejected: new")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("actual")
```

</details>

#### rejects malformed sheet cell references without mutating

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Checked")
val result = sheet.update_cell_checked("not-a-ref", "", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("invalid-cell-ref")
expect(result.actual_value).to_equal("<invalid-ref>")
expect(sheet.cell_count()).to_equal(0)
```

</details>

#### rejects missing sheet cells without creating them

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Checked")
val result = sheet.update_cell_checked("A1", "", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("missing-cell")
expect(result.actual_value).to_equal("<missing-cell>")
expect(sheet.cell_count()).to_equal(0)
```

</details>

#### rejects duplicate sheet action source references

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sheet-edit", "A1|new|next\nA1=old;A01=new")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("duplicate-source-ref")
```

</details>

#### rejects blank sheet action target refs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sheet-edit", "   |old|new\nA1=old")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### updates slide text elements only when expected text matches

- SlideElementKind TextBox
   - Expected: actual equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slide = add_text_box(blank_slide("checked"), "title", "old", 40, 40, 840, 60)
val result = slide_update_text_checked(slide, "title", "old", "new")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.diff).to_equal("@@ slide element title @@\n- old\n+ new")
var actual = "<missing>"
match result.slide.elements[0].kind:
    SlideElementKind.TextBox(content: content):
        actual = content
    _:
        actual = "<not-text>"
expect(actual).to_equal("new")
```

</details>

#### rejects stale slide text updates without mutating

- SlideElementKind TextBox
   - Expected: actual equals `actual`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slide = add_text_box(blank_slide("checked"), "title", "actual", 40, 40, 840, 60)
val result = slide_update_text_checked(slide, "title", "expected", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("stale-slide-element")
expect(result.diff).to_equal("@@ slide element title @@\nexpected: expected\nactual: actual\nrejected: new")
var actual = "<missing>"
match result.slide.elements[0].kind:
    SlideElementKind.TextBox(content: content):
        actual = content
    _:
        actual = "<not-text>"
expect(actual).to_equal("actual")
```

</details>

#### rejects missing slide text elements without mutating

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slide = blank_slide("checked")
val result = slide_update_text_checked(slide, "title", "", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("missing-element")
expect(result.actual_value).to_equal("<missing-element>")
expect(result.slide.elements.len()).to_equal(0)
```

</details>

#### rejects duplicate slide action source ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("slide-edit", "title|new|next\ntitle=old;title=new")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("duplicate-source-id")
```

</details>

#### rejects blank slide action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("slide-edit", "   |old|new\ntitle=old")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank UI label action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-label-edit", "   |Run|Launch\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### preserves escaped pipe label edit values

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ui = office_action_dispatch("ui-label-edit", "button|Run\\|Now|Launch\\|Now\ndesign: Feature\nnode button|Run\\|Now|button|16|16|80|32|primary|controls|action")
val node = office_action_dispatch("edit-sdd-node-label", "A|Alpha\\|Ready\ngraph: Label\nA: Alpha")
val edge = office_action_dispatch("edit-sdd-edge-label", "0|open\\|closed\ngraph: Label\nA: A\nB: B\nA -> B: open")
expect(ui.ok).to_be(true)
expect(ui.output).to_contain("data-label=\"Launch|Now\"")
expect(node.ok).to_be(true)
expect(node.output).to_contain("data-label=\"Alpha|Ready\"")
expect(edge.ok).to_be(true)
expect(edge.output).to_contain("data-label=\"open|closed\"")
```

</details>

#### preserves escaped pipe UI design name edits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-name-edit", "Feature\\|One|Feature\\|Two\ndesign: Feature|One\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.ok).to_be(true)
expect(result.output).to_contain("data-design=\"Feature|Two\"")
```

</details>

#### preserves escaped pipe SDD add labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = office_action_dispatch("add-sdd-node", "C|Choice\\|Ready|accent|decision|diamond|96|64|80|32|front|\ngraph: Add\nA: Alpha")
val edge = office_action_dispatch("add-sdd-edge", "A|B|open\\|closed|primary|flow|orthogonal||right|left\ngraph: Add\nA: Alpha\nB: Beta")
expect(node.ok).to_be(true)
expect(node.output).to_contain("data-label=\"Choice|Ready\"")
expect(edge.ok).to_be(true)
expect(edge.output).to_contain("data-label=\"open|closed\"")
```

</details>

#### rejects blank UI layout action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-layout-edit", "   |16|16|80|32|24|32|96|40\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank UI layout geometry fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-layout-edit", "button|16|16|80|32|   |32|96|40\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### accepts max i32 UI layout size fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-layout-edit", "button|16|16|80|32|24|32|2147483647|40\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.ok).to_be(true)
expect(result.output).to_contain("width: 2147483647px")
```

</details>

#### rejects blank UI auto-layout action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-auto-layout-edit", "   |off|0|0,0,0,0|vertical|8|4,4,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank UI auto-layout fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-auto-layout-edit", "frame|off|   |0,0,0,0|vertical|8|4,4,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed UI auto-layout replacement fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode_result = office_action_dispatch("ui-auto-layout-edit", "frame|off|0|0,0,0,0|diagonal|8|4,4,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container")
val gap_result = office_action_dispatch("ui-auto-layout-edit", "frame|off|0|0,0,0,0|vertical|wide|4,4,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container")
val padding_result = office_action_dispatch("ui-auto-layout-edit", "frame|off|0|0,0,0,0|vertical|8|4,bad,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container")
expect(mode_result.reason).to_equal("invalid-args")
expect(gap_result.reason).to_equal("invalid-args")
expect(padding_result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank UI constraints action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-constraints-edit", "   |left|top|stretch|top\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank UI constraints fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-constraints-edit", "button|left|top|   |top\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed UI constraint replacement fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val horizontal_result = office_action_dispatch("ui-constraints-edit", "button|left|top|wide|top\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val vertical_result = office_action_dispatch("ui-constraints-edit", "button|left|top|stretch|middle\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(horizontal_result.reason).to_equal("invalid-args")
expect(vertical_result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank UI layer action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id_result = office_action_dispatch("ui-layer-edit", "   |controls|9\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val expected_result = office_action_dispatch("ui-layer-edit", "button|   |9\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val new_result = office_action_dispatch("ui-layer-edit", "button|controls|   \ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(id_result.ok).to_be(false)
expect(id_result.reason).to_equal("invalid-args")
expect(expected_result.reason).to_equal("invalid-args")
expect(new_result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank UI style-token action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id_result = office_action_dispatch("ui-style-token-edit", "   |primary|accent\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val expected_result = office_action_dispatch("ui-style-token-edit", "button|   |accent\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val new_result = office_action_dispatch("ui-style-token-edit", "button|primary|   \ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(id_result.ok).to_be(false)
expect(id_result.reason).to_equal("invalid-args")
expect(expected_result.reason).to_equal("invalid-args")
expect(new_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed UI style-token replacement fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-style-token-edit", "button|primary|accent,bad\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank UI CSS edit fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id_result = office_action_dispatch("ui-css-edit", "   |primary|accent\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val expected_result = office_action_dispatch("ui-css-edit", "button|   |accent\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val new_result = office_action_dispatch("ui-css-edit", "button|primary|   \ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(id_result.reason).to_equal("invalid-args")
expect(expected_result.reason).to_equal("invalid-args")
expect(new_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed UI CSS edit replacement tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-css-edit", "button|primary|accent,bad\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed UI edit target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label_result = office_action_dispatch("ui-label-edit", "button bad|Run|Launch\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val layout_result = office_action_dispatch("ui-layout-edit", "button bad|16|16|80|32|24|32|96|40\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val auto_layout_result = office_action_dispatch("ui-auto-layout-edit", "frame bad|off|0|0,0,0,0|vertical|8|4,4,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container")
val constraints_result = office_action_dispatch("ui-constraints-edit", "button bad|left|top|stretch|top\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val layer_result = office_action_dispatch("ui-layer-edit", "button bad|controls|9\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val style_result = office_action_dispatch("ui-style-token-edit", "button bad|primary|accent\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(label_result.reason).to_equal("invalid-args")
expect(layout_result.reason).to_equal("invalid-args")
expect(auto_layout_result.reason).to_equal("invalid-args")
expect(constraints_result.reason).to_equal("invalid-args")
expect(layer_result.reason).to_equal("invalid-args")
expect(style_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed UI read target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val read_result = office_action_dispatch("ui-style-token-read", "button bad\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val inspect_result = office_action_dispatch("ui-inspect-node", "button bad\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(read_result.reason).to_equal("invalid-args")
expect(inspect_result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank duplicate node ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ui_result = office_action_dispatch("ui-duplicate-node", "   |button_copy|20|10\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val sdd_result = office_action_dispatch("duplicate-sdd-node", "A|   |20|10\ngraph: Feature\nA: Alpha x: 0 y: 0 width: 80 height: 20")
expect(ui_result.ok).to_be(false)
expect(ui_result.reason).to_equal("invalid-args")
expect(sdd_result.ok).to_be(false)
expect(sdd_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed duplicate UI node ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-duplicate-node", "button|button copy|20|10\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank duplicate UI node offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("ui-duplicate-node", "button|button_copy|   |10\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank duplicate SDD node offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("duplicate-sdd-node", "A|A_copy|   |10\ngraph: Feature\nA: Alpha x: 0 y: 0 width: 80 height: 20")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank layout selection headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ui_result = office_action_dispatch("ui-align-selection", "left| , , \ndesign: Align\nnode a|A|button|0|0|20|20|primary|1|action")
val sdd_result = office_action_dispatch("align-sdd-selection", "   |A\ngraph: Align\nA: A x: 0 y: 0 width: 20 height: 20")
expect(ui_result.ok).to_be(false)
expect(ui_result.reason).to_equal("invalid-args")
expect(sdd_result.ok).to_be(false)
expect(sdd_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed layout selection ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ui_result = office_action_dispatch("ui-align-selection", "left|a,b bad\ndesign: Align\nnode a|A|button|0|0|20|20|primary|1|action\nnode b|B|button|40|20|20|20|secondary|2|action")
val sdd_result = office_action_dispatch("distribute-sdd-selection", "horizontal|A,B bad,C\ngraph: Dist\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 40 y: 0 width: 20 height: 20\nC: C x: 100 y: 0 width: 20 height: 20")
expect(ui_result.ok).to_be(false)
expect(ui_result.reason).to_equal("invalid-args")
expect(sdd_result.ok).to_be(false)
expect(sdd_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed layout modes and axes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ui_result = office_action_dispatch("ui-align-selection", "diagonal|a,b\ndesign: Align\nnode a|A|button|0|0|20|20|primary|1|action\nnode b|B|button|40|20|20|20|secondary|2|action")
val sdd_result = office_action_dispatch("distribute-sdd-selection", "radial|A,B,C\ngraph: Dist\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 40 y: 0 width: 20 height: 20\nC: C x: 100 y: 0 width: 20 height: 20")
expect(ui_result.ok).to_be(false)
expect(ui_result.reason).to_equal("invalid-args")
expect(sdd_result.ok).to_be(false)
expect(sdd_result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank SDD node value action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("edit-sdd-node-style", "   |accent\ngraph: Style\nA: A x: 0 y: 0 width: 20 height: 20")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### reads SDD node style tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-style-read", "A\ngraph: Style\nA: A @accent warning x: 0 y: 0 width: 20 height: 20")
val invalid = office_action_dispatch("sdd-node-style-read", "A bad\ngraph: Style\nA: A @accent")
val missing = office_action_dispatch("sdd-node-style-read", "Nope\ngraph: Style\nA: A @accent")
expect(result.ok).to_be(true)
expect(result.output).to_equal("accent warning")
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("invalid-args")
expect(missing.ok).to_be(false)
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads SDD node labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-label-read", "A\ngraph: Label\nA: Alpha Label")
val invalid = office_action_dispatch("sdd-node-label-read", "A bad\ngraph: Label\nA: Alpha")
val missing = office_action_dispatch("sdd-node-label-read", "Nope\ngraph: Label\nA: Alpha")
expect(result.ok).to_be(true)
expect(result.output).to_equal("Alpha Label")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads SDD edge style tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-style-read", "0\ngraph: Style\nA: A\nB: B\nA -> B: link @warning dashed")
val invalid = office_action_dispatch("sdd-edge-style-read", "bad\ngraph: Style\nA: A\nB: B\nA -> B: link @warning")
val missing = office_action_dispatch("sdd-edge-style-read", "2\ngraph: Style\nA: A\nB: B\nA -> B: link @warning")
expect(result.ok).to_be(true)
expect(result.output).to_equal("warning dashed")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### rejects escaped pipe SDD edge style tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("edit-sdd-edge-style", "0|warning\\|dashed\ngraph: Style\nA: A\nB: B\nA -> B: link @warning")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-style-token")
expect(result.output).to_contain("actual: warning|dashed")
```

</details>

#### reads resolved SDD edge styles

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-resolved-style-read", "0\ngraph: Style\ncss base:\n    stroke: #111111\ncss critical:\n    extends: base\n    fill: #eeeeee\nA: A\nB: B\nA -> B: link @critical")
val invalid = office_action_dispatch("sdd-edge-resolved-style-read", "bad\ngraph: Style\nA: A\nB: B\nA -> B: link @critical")
val missing = office_action_dispatch("sdd-edge-resolved-style-read", "2\ngraph: Style\nA: A\nB: B\nA -> B: link @critical")
expect(result.ok).to_be(true)
expect(result.output).to_contain("stroke:#111111")
expect(result.output).to_contain("fill:#eeeeee")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### reads resolved SDD edge style values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-resolved-style-value-read", "0|stroke\ngraph: Style\ncss base:\n    stroke: #111111\ncss critical:\n    extends: base\n    fill: #eeeeee\nA: A\nB: B\nA -> B: link @critical")
val invalid = office_action_dispatch("sdd-edge-resolved-style-value-read", "0|bad key\ngraph: Style\nA: A\nB: B\nA -> B: link @critical")
val missing = office_action_dispatch("sdd-edge-resolved-style-value-read", "2|stroke\ngraph: Style\nA: A\nB: B\nA -> B: link @critical")
expect(result.ok).to_be(true)
expect(result.output).to_equal("#111111")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### reads SDD edge labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-label-read", "0\ngraph: Label\nA: A\nB: B\nA -> B: approved")
val invalid = office_action_dispatch("sdd-edge-label-read", "bad\ngraph: Label\nA: A\nB: B\nA -> B: approved")
val missing = office_action_dispatch("sdd-edge-label-read", "2\ngraph: Label\nA: A\nB: B\nA -> B: approved")
expect(result.ok).to_be(true)
expect(result.output).to_equal("approved")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### reads SDD edge label points

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-label-point-read", "0\ngraph: Point\nA: A\nB: B\nA -> B: approved label_x: 66 label_y: -12")
val invalid = office_action_dispatch("sdd-edge-label-point-read", "bad\ngraph: Point\nA: A\nB: B\nA -> B: approved")
val missing = office_action_dispatch("sdd-edge-label-point-read", "2\ngraph: Point\nA: A\nB: B\nA -> B: approved")
expect(result.ok).to_be(true)
expect(result.output).to_equal("66,-12")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### reads SDD edge kind tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-kind-read", "0\ngraph: Kind\nA: A\nB: B\nA -> B: link kind: async")
val invalid = office_action_dispatch("sdd-edge-kind-read", "bad\ngraph: Kind\nA: A\nB: B\nA -> B: link kind: async")
val missing = office_action_dispatch("sdd-edge-kind-read", "2\ngraph: Kind\nA: A\nB: B\nA -> B: link kind: async")
expect(result.ok).to_be(true)
expect(result.output).to_equal("async")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### rejects escaped pipe SDD edge kind tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("edit-sdd-edge-kind", "0|async\\|reply\ngraph: Kind\nA: A\nB: B\nA -> B: link kind: async")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-kind-token")
expect(result.output).to_contain("actual: async|reply")
```

</details>

#### reads SDD edge endpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-endpoints-read", "0\ngraph: Endpoints\nA: A\nB: B\nA -> B: link")
val invalid = office_action_dispatch("sdd-edge-endpoints-read", "bad\ngraph: Endpoints\nA: A\nB: B\nA -> B: link")
val missing = office_action_dispatch("sdd-edge-endpoints-read", "2\ngraph: Endpoints\nA: A\nB: B\nA -> B: link")
expect(result.ok).to_be(true)
expect(result.output).to_equal("A,B")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### reads SDD edge routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-route-read", "0\ngraph: Route\nA: A\nB: B\nA -> B: link route: orthogonal waypoints: 40x10 start: right end: left")
val invalid = office_action_dispatch("sdd-edge-route-read", "bad\ngraph: Route\nA: A\nB: B\nA -> B: link")
val missing = office_action_dispatch("sdd-edge-route-read", "2\ngraph: Route\nA: A\nB: B\nA -> B: link")
expect(result.ok).to_be(true)
expect(result.output).to_equal("orthogonal|40x10|right|left")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### reads SDD edge paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-path-read", "0\ngraph: Path\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 80 y: 0 width: 20 height: 20\nA -> B: link route: orthogonal waypoints: 40x10 start: right end: left")
val invalid = office_action_dispatch("sdd-edge-path-read", "bad\ngraph: Path\nA: A\nB: B\nA -> B: link")
val missing = office_action_dispatch("sdd-edge-path-read", "2\ngraph: Path\nA: A\nB: B\nA -> B: link")
expect(result.ok).to_be(true)
expect(result.output).to_contain("M")
expect(result.output).to_contain("|20,10,80,10|2")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### reads SDD edge segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-edge-segments-read", "0\ngraph: Segments\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 80 y: 0 width: 20 height: 20\nA -> B: link route: orthogonal waypoints: 40x10 start: right end: left")
val invalid = office_action_dispatch("sdd-edge-segments-read", "bad\ngraph: Segments\nA: A\nB: B\nA -> B: link")
val missing = office_action_dispatch("sdd-edge-segments-read", "2\ngraph: Segments\nA: A\nB: B\nA -> B: link")
expect(result.ok).to_be(true)
expect(result.output).to_equal("20,10-40,10;40,10-80,10|30,10;60,10|h;h")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-edge")
```

</details>

#### rejects blank SDD node geometry action target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("edit-sdd-node-geometry", "   |0|0|20|20\ngraph: Geometry\nA: A x: 0 y: 0 width: 20 height: 20")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### reads SDD node geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-geometry-read", "A\ngraph: Geometry\nA: A x: -4 y: 8 width: 40 height: 24")
val invalid = office_action_dispatch("sdd-node-geometry-read", "A bad\ngraph: Geometry\nA: A")
val missing = office_action_dispatch("sdd-node-geometry-read", "Nope\ngraph: Geometry\nA: A")
expect(result.ok).to_be(true)
expect(result.output).to_equal("-4,8,40,24")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads SDD node shapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-shape-read", "A\ngraph: Shape\nA: A shape: diamond")
val invalid = office_action_dispatch("sdd-node-shape-read", "A bad\ngraph: Shape\nA: A")
val missing = office_action_dispatch("sdd-node-shape-read", "Nope\ngraph: Shape\nA: A")
expect(result.ok).to_be(true)
expect(result.output).to_equal("diamond")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads SDD node layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-layer-read", "A\ngraph: Layer\nA: A layer: foreground")
val invalid = office_action_dispatch("sdd-node-layer-read", "A bad\ngraph: Layer\nA: A")
val missing = office_action_dispatch("sdd-node-layer-read", "Nope\ngraph: Layer\nA: A")
expect(result.ok).to_be(true)
expect(result.output).to_equal("foreground")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads SDD node roles

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-role-read", "A\ngraph: Role\nA: A role: datastore")
val invalid = office_action_dispatch("sdd-node-role-read", "A bad\ngraph: Role\nA: A")
val missing = office_action_dispatch("sdd-node-role-read", "Nope\ngraph: Role\nA: A")
expect(result.ok).to_be(true)
expect(result.output).to_equal("datastore")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads SDD node parents

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-parent-read", "B\ngraph: Parent\nA: A\nB: B parent: A")
val invalid = office_action_dispatch("sdd-node-parent-read", "B bad\ngraph: Parent\nA: A\nB: B parent: A")
val missing = office_action_dispatch("sdd-node-parent-read", "Nope\ngraph: Parent\nA: A\nB: B parent: A")
expect(result.ok).to_be(true)
expect(result.output).to_equal("A")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads SDD node child bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-child-bounds-read", "A\ngraph: Parent\nA: A x: 0 y: 0 width: 100 height: 100\nB: B x: 10 y: 20 width: 30 height: 40 parent: A\nC: C x: 50 y: 5 width: 10 height: 10 parent: A")
val invalid = office_action_dispatch("sdd-node-child-bounds-read", "A bad\ngraph: Parent\nA: A")
val missing = office_action_dispatch("sdd-node-child-bounds-read", "Nope\ngraph: Parent\nA: A")
expect(result.ok).to_be(true)
expect(result.output).to_equal("10,5,60,60")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads SDD node child counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-child-count-read", "A\ngraph: Parent\nA: A x: 0 y: 0 width: 100 height: 100\nB: B x: 10 y: 20 width: 30 height: 40 parent: A\nC: C x: 50 y: 5 width: 10 height: 10 parent: A")
val invalid = office_action_dispatch("sdd-node-child-count-read", "A bad\ngraph: Parent\nA: A")
val missing = office_action_dispatch("sdd-node-child-count-read", "Nope\ngraph: Parent\nA: A")
expect(result.ok).to_be(true)
expect(result.output).to_equal("2")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads resolved SDD node styles

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-resolved-style-read", "A\ngraph: Style\ncss base:\n    stroke: #111111\ncss accent:\n    extends: base\n    fill: #eeeeee\nA: A @accent")
val invalid = office_action_dispatch("sdd-node-resolved-style-read", "A bad\ngraph: Style\nA: A @accent")
val missing = office_action_dispatch("sdd-node-resolved-style-read", "Nope\ngraph: Style\nA: A @accent")
expect(result.ok).to_be(true)
expect(result.output).to_contain("border-color:#111111")
expect(result.output).to_contain("background-color:#eeeeee")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### reads resolved SDD node style values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-resolved-style-value-read", "A|stroke\ngraph: Style\ncss base:\n    stroke: #111111\ncss accent:\n    extends: base\n    fill: #eeeeee\nA: A @accent")
val invalid = office_action_dispatch("sdd-node-resolved-style-value-read", "A|bad key\ngraph: Style\nA: A @accent")
val missing = office_action_dispatch("sdd-node-resolved-style-value-read", "Nope|stroke\ngraph: Style\nA: A @accent")
expect(result.ok).to_be(true)
expect(result.output).to_equal("#111111")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### rejects blank SDD node order target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("order-sdd-node", "   |front\ngraph: Order\nA: A\nB: B")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### reads SDD node order indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-node-order-read", "B\ngraph: Order\nA: A\nB: B")
val invalid = office_action_dispatch("sdd-node-order-read", "B bad\ngraph: Order\nA: A\nB: B")
val missing = office_action_dispatch("sdd-node-order-read", "Nope\ngraph: Order\nA: A\nB: B")
expect(result.ok).to_be(true)
expect(result.output).to_equal("1")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-node")
```

</details>

#### rejects blank SDD canvas fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("edit-sdd-canvas", "640|480|16|true|125|   \ngraph: Canvas\nA: A")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed SDD canvas fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val number_result = office_action_dispatch("edit-sdd-canvas", "640|480|16;bad|true|125|#ffffff\ngraph: Canvas\nA: A")
val long_number_result = office_action_dispatch("edit-sdd-canvas", "1000000000|480|16|true|125|#ffffff\ngraph: Canvas\nA: A")
val snap_result = office_action_dispatch("edit-sdd-canvas", "640|480|16|yes|125|#ffffff\ngraph: Canvas\nA: A")
val background_result = office_action_dispatch("edit-sdd-canvas", "640|480|16|true|125|url(javascript:bad)\ngraph: Canvas\nA: A")
val escaped_pipe_result = office_action_dispatch("edit-sdd-canvas", "640|480|16|true|125|#fff\\|#000\ngraph: Canvas\nA: A")
expect(number_result.reason).to_equal("invalid-canvas-number")
expect(long_number_result.reason).to_equal("invalid-canvas-number")
expect(snap_result.reason).to_equal("invalid-canvas-snap")
expect(background_result.reason).to_equal("invalid-canvas-background")
expect(escaped_pipe_result.reason).to_equal("invalid-canvas-background")
```

</details>

#### rejects blank SDD style rule keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inspect_result = office_action_dispatch("inspect-sdd-style-rule", "accent|   \ngraph: Style\nstyle accent |node| fill: #eeeeee\nA: A @accent")
val delete_result = office_action_dispatch("delete-sdd-style-rule", "accent|   \ngraph: Style\nstyle accent |node| fill: #eeeeee\nA: A @accent")
expect(inspect_result.ok).to_be(false)
expect(inspect_result.reason).to_equal("invalid-args")
expect(delete_result.ok).to_be(false)
expect(delete_result.reason).to_equal("invalid-args")
```

</details>

#### reads SDD style rule extends

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-style-extends-read", "accent|fill\ngraph: Style\ncss base:\n    fill: #ffffff\ncss accent:\n    extends: base\n    fill: #eeeeee\nA: A @accent")
val invalid = office_action_dispatch("sdd-style-extends-read", "accent,bad|fill\ngraph: Style\ncss accent:\n    fill: #eeeeee")
val missing = office_action_dispatch("sdd-style-extends-read", "accent|stroke\ngraph: Style\ncss accent:\n    fill: #eeeeee")
expect(result.ok).to_be(true)
expect(result.output).to_equal("base")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-style-rule")
```

</details>

#### reads SDD style rule targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-style-target-read", "accent|fill\ngraph: Style\ncss accent:\n    fill: #eeeeee\nA: A @accent")
val invalid = office_action_dispatch("sdd-style-target-read", "accent,bad|fill\ngraph: Style\ncss accent:\n    fill: #eeeeee")
val missing = office_action_dispatch("sdd-style-target-read", "accent|stroke\ngraph: Style\ncss accent:\n    fill: #eeeeee")
expect(result.ok).to_be(true)
expect(result.output).to_equal("node")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-style-rule")
```

</details>

#### reads SDD style rule values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-style-value-read", "accent|fill\ngraph: Style\ncss accent:\n    fill: #eeeeee\nA: A @accent")
val invalid = office_action_dispatch("sdd-style-value-read", "accent,bad|fill\ngraph: Style\ncss accent:\n    fill: #eeeeee")
val missing = office_action_dispatch("sdd-style-value-read", "accent|stroke\ngraph: Style\ncss accent:\n    fill: #eeeeee")
expect(result.ok).to_be(true)
expect(result.output).to_equal("#eeeeee")
expect(invalid.reason).to_equal("invalid-args")
expect(missing.reason).to_equal("missing-style-rule")
```

</details>

#### reads resolved SDD style values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-style-resolved-value-read", "accent|node|stroke\ngraph: Style\ncss base:\n    stroke: #111111\ncss accent:\n    extends: base\n    fill: #eeeeee\nA: A @accent")
val invalid = office_action_dispatch("sdd-style-resolved-value-read", "accent|canvas|stroke\ngraph: Style\ncss accent:\n    fill: #eeeeee")
expect(result.ok).to_be(true)
expect(result.output).to_equal("#111111")
expect(invalid.reason).to_equal("invalid-args")
```

</details>

#### reads resolved SDD style declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("sdd-style-resolved-read", "accent|node\ngraph: Style\ncss base:\n    stroke: #111111\ncss accent:\n    extends: base\n    fill: #eeeeee\nA: A @accent")
val invalid = office_action_dispatch("sdd-style-resolved-read", "accent|canvas\ngraph: Style\ncss accent:\n    fill: #eeeeee")
expect(result.ok).to_be(true)
expect(result.output).to_contain("border-color:#111111")
expect(result.output).to_contain("background-color:#eeeeee")
expect(invalid.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed SDD inspect ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node_result = office_action_dispatch("inspect-sdd-node", "A bad\ngraph: Inspect\nA: A")
val style_result = office_action_dispatch("inspect-sdd-style-rule", "accent,bad|fill\ngraph: Style\nstyle accent |node| fill: #eeeeee\nA: A @accent")
expect(node_result.reason).to_equal("invalid-args")
expect(style_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed SDD style rule delete keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("delete-sdd-style-rule", "accent,bad|fill\ngraph: Style\nstyle accent |node| fill: #eeeeee\nA: A @accent")
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed SDD edit target ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duplicate_result = office_action_dispatch("duplicate-sdd-node", "A bad|A_copy|20|10\ngraph: Feature\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val style_result = office_action_dispatch("edit-sdd-node-style", "A bad|accent\ngraph: Style\nA: A x: 0 y: 0 width: 20 height: 20")
val geometry_result = office_action_dispatch("edit-sdd-node-geometry", "A bad|0|0|20|20\ngraph: Geometry\nA: A x: 0 y: 0 width: 20 height: 20")
val order_result = office_action_dispatch("order-sdd-node", "A bad|front\ngraph: Order\nA: A\nB: B")
val delete_result = office_action_dispatch("delete-sdd-node", "A bad\ngraph: Delete\nA: A")
val parent_result = office_action_dispatch("edit-sdd-node-parent", "A|Bad Parent\ngraph: Parent\nA: A\nB: B")
val missing_parent_target_result = office_action_dispatch("edit-sdd-node-parent", "Nope|Bad Parent\ngraph: Parent\nA: A\nB: B")
expect(duplicate_result.reason).to_equal("invalid-args")
expect(style_result.reason).to_equal("invalid-args")
expect(geometry_result.reason).to_equal("invalid-args")
expect(order_result.reason).to_equal("invalid-args")
expect(delete_result.reason).to_equal("invalid-args")
expect(parent_result.reason).to_equal("invalid-args")
expect(missing_parent_target_result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank SDD style rule edit fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("edit-sdd-style-rule", "accent|node|none|   |#eeeeee\ngraph: Style\nA: A @accent")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### rejects escaped pipe SDD style rule values as unsafe CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("edit-sdd-style-rule", "accent|node||stroke-dasharray|4\\|2\ngraph: Style\nA: A @accent")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-style-value")
expect(result.output).to_contain("actual: 4|2")
```

</details>

#### rejects blank SDD edge endpoint ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add_result = office_action_dispatch("add-sdd-edge", "   |A|link|primary|flow|simple||right|left\ngraph: Edge\nA: A")
val edit_result = office_action_dispatch("edit-sdd-edge-endpoints", "0|A|   \ngraph: Edge\nA: A\nB: B\nA -> B: link")
expect(add_result.ok).to_be(false)
expect(add_result.reason).to_equal("invalid-args")
expect(edit_result.ok).to_be(false)
expect(edit_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed SDD edge endpoint ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add_result = office_action_dispatch("add-sdd-edge", "A bad|B|link|primary|flow|simple||right|left\ngraph: Edge\nA: A\nB: B")
val edit_result = office_action_dispatch("edit-sdd-edge-endpoints", "0|A|B bad\ngraph: Edge\nA: A\nB: B\nA -> B: link")
expect(add_result.reason).to_equal("invalid-args")
expect(edit_result.reason).to_equal("invalid-args")
```

</details>

#### rejects malformed SDD add edge route fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route_result = office_action_dispatch("add-sdd-edge", "B|A|return|secondary|reply|curve||left|right\ngraph: Edge\nA: A\nB: B")
val waypoint_result = office_action_dispatch("add-sdd-edge", "B|A|return|secondary|reply|orthogonal|60xbad|left|right\ngraph: Edge\nA: A\nB: B")
val anchor_result = office_action_dispatch("add-sdd-edge", "B|A|return|secondary|reply|orthogonal|60x10|side|right\ngraph: Edge\nA: A\nB: B")
expect(route_result.reason).to_equal("invalid-args")
expect(waypoint_result.reason).to_equal("invalid-args")
expect(anchor_result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank SDD edge label point coordinates

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blank_result = office_action_dispatch("edit-sdd-edge-label-point", "0|   |12\ngraph: Edge\nA: A\nB: B\nA -> B: link")
val malformed_result = office_action_dispatch("edit-sdd-edge-label-point", "0|bad\"x|12\ngraph: Edge\nA: A\nB: B\nA -> B: link")
val negative_result = office_action_dispatch("edit-sdd-edge-label-point", "0|-4|12\ngraph: Edge\nA: A\nB: B\nA -> B: link")
expect(blank_result.ok).to_be(false)
expect(blank_result.reason).to_equal("invalid-args")
expect(malformed_result.reason).to_equal("invalid-args")
expect(negative_result.ok).to_be(true)
```

</details>

#### rejects malformed SDD reroute connector fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route_result = office_action_dispatch("reroute-sdd-connector", "0|curve|60x10|right|left\ngraph: Route\nA: A\nB: B\nA -> B: link")
val waypoint_result = office_action_dispatch("reroute-sdd-connector", "0|orthogonal|60xbad|right|left\ngraph: Route\nA: A\nB: B\nA -> B: link")
val anchor_result = office_action_dispatch("reroute-sdd-connector", "0|orthogonal|60x10|side|left\ngraph: Route\nA: A\nB: B\nA -> B: link")
expect(route_result.reason).to_equal("invalid-args")
expect(waypoint_result.reason).to_equal("invalid-args")
expect(anchor_result.reason).to_equal("invalid-args")
```

</details>

#### rejects blank SDD add node geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("add-sdd-node", "C|Choice|accent|decision|diamond|   |64|48|32|front|\ngraph: Node Add\nA: Alpha")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### keeps blank SDD add node ids as invalid ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("add-sdd-node", "   |Choice|accent|decision|diamond|32|64|48|32|front|\ngraph: Node Add\nA: Alpha")
val malformed = office_action_dispatch("add-sdd-node", "   |Choice|accent|decision|diamond|   |64|48|32|front|\ngraph: Node Add\nA: Alpha")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-id")
expect(malformed.ok).to_be(false)
expect(malformed.reason).to_equal("invalid-args")
```

</details>

#### replaces the first office search match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_search_options()
val result = replace_first("draft draft", "draft", "final", 0, options)
expect(result).to_equal("final draft")
```

</details>

#### uses a stable unset planner priority without command warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = new_task("task_0", "Backlog")
expect(priority_name(task.priority)).to_equal("None")
expect(priority_icon(task.priority)).to_equal("-")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 168 |
| Active scenarios | 168 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/ide_office_plugin_suite.md](doc/03_plan/sys_test/ide_office_plugin_suite.md)
- **Design:** [doc/07_guide/app/ide_office_plugin_suite.md](doc/07_guide/app/ide_office_plugin_suite.md)


</details>
