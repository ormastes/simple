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
| 110 | 110 | 0 | 0 |

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
LLM-catalog action is recognized by the dispatcher and no advertised action
falls through to `unknown-action`.

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

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["open_word"])).to_equal(0)
expect(run_office(["open_sheets"])).to_equal(0)
expect(run_office(["open_slides"])).to_equal(0)
expect(run_office(["open_draw"])).to_equal(0)
expect(run_office(["open_db"])).to_equal(0)
expect(run_office(["open_math"])).to_equal(0)
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

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1=old;B1=2"])).to_equal(0)
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

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "title=old;body=second"])).to_equal(0)
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

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-writer-markdown-html", "# Title\\n\\nBody")
expect(result.ok).to_be(true)
expect(result.code).to_equal(0)
expect(result.output).to_contain("class=\"md-paper\"")
expect(result.output).to_contain("data-format=\"markdown-paper\"")
expect(result.output).to_contain("Title")
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

#### dispatches UI render and SDD export catalog actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "design: Feature\\nsize: 640x480\\nnode button|Run|button|16|20|96|32|primary|controls|action"
val html = office_action_dispatch("render-ui-html", source)
val selected_html = office_action_dispatch("render-ui-html-with-selection", "select|button\\n" + source)
val invalid_selected_html = office_action_dispatch("render-ui-html-with-selection", "select|button bad\\n" + source)
val sdd = office_action_dispatch("export-ui-sdd", source)
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
expect(legacy_html.action).to_equal("render-ui-html")
expect(legacy_html.output).to_contain("data-format=\"html-ui\"")
expect(legacy_sdd.action).to_equal("export-ui-sdd")
expect(legacy_sdd.output).to_contain("graph: Feature")
```

</details>

#### dispatches selected SDD HTML rendering from the Draw catalog action

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-sdd-html-with-selection", "graph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val selected = office_action_dispatch("render-sdd-html-with-selection", "select|A|\\ngraph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val invalid = office_action_dispatch("render-sdd-html-with-selection", "select|A bad|\\ngraph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val legacy = office_action_dispatch("render-sdd", "graph: Feature\\nA: Alpha x: 0 y: 0 width: 80 height: 20")
expect(result.ok).to_be(true)
expect(result.output).to_contain("class=\"sdn-graph sdd-diagram\"")
expect(result.output).to_contain("data-node=\"A\"")
expect(result.output).to_contain("data-selected-node-id=\"\"")
expect(result.output).to_contain("data-selected-edge-index=\"-1\"")
expect(selected.ok).to_be(true)
expect(selected.output).to_contain("data-selected-node-id=\"A\"")
expect(selected.output).to_contain("data-selected=\"true\"")
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

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("render-base-table-html", "table: Feature\\ncolumns: id,status\\nrow: 1,<open>")
expect(result.ok).to_be(true)
expect(result.output).to_contain("scope=\"col\" data-column=\"status\"")
expect(result.output).to_contain("<tr data-row-index=\"0\">")
expect(result.output).to_contain("<td data-column=\"status\">&lt;open&gt;</td>")
```

</details>

#### rejects malformed Base table queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("query-table", "count-where|status|open\\ntable: Bad\\ncolumns: id,status\\nrow: 1")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("row-width-mismatch")
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

#### rejects blank Base table columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("db-edit", "insert|2,done,done\\ntable: Bad\\ncolumns: id,,status\\nrow: 1,open,open")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("blank-column")
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

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("counter-action", "5|   ")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-args")
```

</details>

#### recognizes every LLM catalog office action

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = office_catalog_dispatch_probe()
expect(probe.advertised_count).to_equal(56)
expect(probe.recognized_count).to_equal(56)
expect(probe.missing_actions.len()).to_equal(0)
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

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(launcher_action_allowlist().len()).to_equal(9)
expect(launcher_open_action("word")).to_equal("open_word")
expect(is_valid_launcher_action("open_word")).to_be(true)
expect(is_valid_launcher_action("open_draw")).to_be(true)
expect(is_valid_launcher_action("open_db")).to_be(true)
expect(is_valid_launcher_action("open_math")).to_be(true)
expect(is_valid_launcher_action("open_counter")).to_be(true)
val slides = launcher_action_to_component("open_slides")
expect(slides.is_some()).to_be(true)
expect(slides.unwrap()).to_equal("slides")
val draw = launcher_action_to_component("open_draw")
expect(draw.is_some()).to_be(true)
expect(draw.unwrap()).to_equal("draw")
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val number_result = office_action_dispatch("edit-sdd-canvas", "640|480|16;bad|true|125|#ffffff\ngraph: Canvas\nA: A")
val long_number_result = office_action_dispatch("edit-sdd-canvas", "1000000000|480|16|true|125|#ffffff\ngraph: Canvas\nA: A")
val snap_result = office_action_dispatch("edit-sdd-canvas", "640|480|16|yes|125|#ffffff\ngraph: Canvas\nA: A")
val background_result = office_action_dispatch("edit-sdd-canvas", "640|480|16|true|125|url(javascript:bad)\ngraph: Canvas\nA: A")
expect(number_result.reason).to_equal("invalid-canvas-number")
expect(long_number_result.reason).to_equal("invalid-canvas-number")
expect(snap_result.reason).to_equal("invalid-canvas-snap")
expect(background_result.reason).to_equal("invalid-canvas-background")
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

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_action_dispatch("add-sdd-node", "   |Choice|accent|decision|diamond|   |64|48|32|front|\ngraph: Node Add\nA: Alpha")
expect(result.ok).to_be(false)
expect(result.reason).to_equal("invalid-id")
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
| Total scenarios | 110 |
| Active scenarios | 110 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/ide_office_plugin_suite.md](doc/03_plan/sys_test/ide_office_plugin_suite.md)
- **Design:** [doc/07_guide/app/ide_office_plugin_suite.md](doc/07_guide/app/ide_office_plugin_suite.md)


</details>
