# ide_office_plugin_suite_spec

> Validates that IDE-facing Markdown, presentation, spreadsheet, dashboard, database, and LibreOffice-like app catalog surfaces reuse existing app modules.

<!-- sdn-diagram:id=ide_office_plugin_suite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_office_plugin_suite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_office_plugin_suite_spec -> std
ide_office_plugin_suite_spec -> app
ide_office_plugin_suite_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_office_plugin_suite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ide_office_plugin_suite_spec

Validates that IDE-facing Markdown, presentation, spreadsheet, dashboard, database, and LibreOffice-like app catalog surfaces reuse existing app modules.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/ide_office_plugin_suite.md |
| Design | doc/05_design/app/office/libreoffice_llm_access.md |
| Research | doc/01_research/app/office/libreoffice_llm_access.md |
| Source | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that IDE-facing Markdown, presentation, spreadsheet, dashboard,
database, and LibreOffice-like app catalog surfaces reuse existing app modules.

## Examples

`simple ide --feature-check --tui` and `simple ide --feature-check --gui` expose
the same app catalog, edit-command checks, plugin manifest, and LLM-readable app
feature list.

**Requirements:** N/A
**Plan:** doc/03_plan/sys_test/ide_office_plugin_suite.md
**Design:** doc/05_design/app/office/libreoffice_llm_access.md
**Research:** doc/01_research/app/office/libreoffice_llm_access.md

**TUI Captures:** build/test-artifacts/03_system/app/ide/feature/ide_office_plugin_suite/feature_check_tui.txt

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `feature_check_tui.txt` | TUI capture | `build/test-artifacts/03_system/app/ide/feature/ide_office_plugin_suite/feature_check_tui.txt` |

#### Embedded TUI Text Captures

<details>
<summary>feature_check_tui.txt</summary>

```text
Simple IDE feature check
mode: tui
capabilities: 6
markdown: Markdown Preview [document-renderer] -> std.editor.render.md_renderer (md, markdown)
  check: markdown: std.editor.render.md_renderer blocks=3 lines=6 preview=6 heading=true table=true css_doc=true escaped=true metadata=true
  edit-command: md-edit=true stale-reject=true reason=stale-line
slides: Presentation Slides [office-app] -> app.office.slides (ppt, presentation, slides)
  check: slides: app.office.slides count=2 thumb=Slide 2: Roadmap canvas=2 outline=2 designs=2 css=true transform=true ppt_html=true safe_css=true positioned=true element_meta=true
  edit-command: slide-edit=true stale-reject=true reason=stale-slide-element
draw: SDD Diagram Draw [office-app] -> std.editor.services.sdn_graph (draw, diagram, sdd, sdn)
  check: draw: sdn_graph format=sdd name="SDD: Simple Diagram Document" extension=.sdd.sdn nodes=3 edges=2 html=true route=true select=true inspect=true child_meta=true path_meta=true edit=true geometry=true layer=true order=true role=true node_create=true style_rule=true style_delete=true style_inspect=true edge_create=true edge_duplicate=true edge_label_point=true edge_style=true edge_kind=true reconnect=true delete=true node_delete=true layout=true canvas=true
sheets: Spreadsheet [office-app] -> app.office.sheets (excel, xlsx, tabular, csv)
  check: sheets: app.office.sheets formats=excel,xlsx,csv,tabular range=A1:C1 formula=5 evaluator=true display_recalc=true
  edit-command: sheet-edit=true stale-reject=true reason=stale-cell
  gui: gui-backend: theme=dark size=1200x800 md=true ppt=true sheet=true config=true
agent-dashboard: Agent Dashboard [dashboard] -> app.editor.mcp_tools (agent, dashboard, mcp)
  check: agent-dashboard: tools=19 lsp=10 wiki=3 modes=3 team=3 blocked=2 status=degraded-review-required
db-admin: Database Admin [database] -> std.editor.core.session_db (embedded-db, simple-db, portal-db)
  check: db-admin: owners=5 targets=4 state=normal/1 contracts=Rel/BlkNo/Lsn/TxnId/PhysPtr/PageBuf page-size=4096
  tui: tui-panels: preview=4 outline=2 md=true table=true slide-outline=true styled=true
  launch: launch: tui=tui gui=gui sdl=gui-sdl files=3 office_actions=9 office_cards=9 unknown=--bad-mode
  plugin-manifest: plugins: entries=6 roundtrip=6 names=6 libre=6 libre_roundtrip=6
  llm-catalog: apps=9 features=97 actions=56
  llm-apps: Markdown,Writer,Calc,Impress,Draw,Designer,Base,Math,Counter
```

</details>

## Scenarios

### IDE office plugin suite capabilities

#### registers markdown slides sheets dashboard and database capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ids = ide_capability_ids().join(",")
expect(ids).to_contain("markdown")
expect(ids).to_contain("slides")
expect(ids).to_contain("draw")
expect(ids).to_contain("sheets")
expect(ids).to_contain("agent-dashboard")
expect(ids).to_contain("db-admin")
```

</details>

#### points each capability at an existing implementation owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = ide_capabilities()
var owners = ""
for cap in caps:
    owners = owners + cap.owner_module + "\n"
expect(owners).to_contain("std.editor.render.md_renderer")
expect(owners).to_contain("app.office.slides")
expect(owners).to_contain("std.editor.services.sdn_graph")
expect(owners).to_contain("app.office.sheets")
expect(owners).to_contain("app.editor.mcp_tools")
expect(owners).to_contain("std.editor.core.session_db")
```

</details>

#### reports GUI and TUI feature checks through the IDE product surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tui_report = ide_feature_check_report("tui").join("\n")
val gui_report = ide_feature_check_report("gui").join("\n")
var registry_checks = ""
for cap in ide_capabilities():
    registry_checks = registry_checks + cap.feature_check + "\n"
expect(tui_report).to_contain("mode: tui")
expect(gui_report).to_contain("mode: gui")
expect(tui_report).to_contain("Presentation Slides")
expect(tui_report).to_contain("draw: SDD Diagram Draw")
expect(tui_report).to_contain("name=\"SDD: Simple Diagram Document\"")
expect(tui_report).to_contain("extension=.sdd.sdn")
expect(tui_report).to_contain("draw: sdn_graph")
expect(tui_report).to_contain("layout=true")
expect(tui_report).to_contain("canvas=true")
expect(gui_report).to_contain("Database Admin")
expect(tui_report).to_contain("tui-panels:")
expect(tui_report).to_contain("slides: app.office.slides")
expect(tui_report).to_contain("edit-command: md-edit=true stale-reject=true")
expect(tui_report).to_contain("metadata=true")
expect(tui_report).to_contain("edit-command: slide-edit=true stale-reject=true")
expect(tui_report).to_contain("edit-command: sheet-edit=true stale-reject=true")
expect(tui_report).to_contain("display_recalc=true")
expect(tui_report).to_contain("agent-dashboard: tools=")
expect(tui_report).to_contain("status=degraded-review-required")
expect(tui_report).to_contain("llm-catalog: apps=9")
expect(tui_report).to_contain("llm-apps: Markdown,Writer,Calc,Impress,Draw,Designer,Base,Math,Counter")
expect(tui_report).to_contain("office_actions=9")
expect(tui_report).to_contain("office_cards=9")
expect(tui_report).to_contain("libre=6")
expect(tui_report).to_contain("libre_roundtrip=6")
expect(registry_checks).to_contain("metadata=true")
expect(registry_checks).to_contain("ppt_html=true")
expect(registry_checks).to_contain("path_meta=true")
expect(registry_checks).to_contain("display_recalc=true")
expect(registry_checks).to_contain("contracts=true")
```

</details>

#### keeps the feature-check manual surface complete and ordered

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ide_feature_check_report("tui")
expect(lines.len()).to_equal(24)
expect(lines[0]).to_equal("Simple IDE feature check")
expect(lines[1]).to_equal("mode: tui")
expect(lines[2]).to_equal("capabilities: 6")
expect(lines[3]).to_start_with("markdown:")
expect(lines[5]).to_start_with("  edit-command:")
expect(lines[6]).to_start_with("slides:")
expect(lines[8]).to_start_with("  edit-command:")
expect(lines[9]).to_start_with("draw:")
expect(lines[10]).to_start_with("  check:")
expect(lines[11]).to_start_with("sheets:")
expect(lines[13]).to_start_with("  edit-command:")
expect(lines[15]).to_start_with("agent-dashboard:")
expect(lines[17]).to_start_with("db-admin:")
expect(lines[21]).to_start_with("  plugin-manifest:")
expect(lines[22]).to_start_with("  llm-catalog:")
expect(lines[23]).to_start_with("  llm-apps:")
```

</details>

#### keeps the TUI feature-check layout within terminal width and captures it

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ide_feature_check_report("tui")
val capture = lines.join("\n")
expect(_max_line_width(lines)).to_be_less_than(121)
expect(capture).to_contain("markdown: Markdown Preview")
expect(capture).to_contain("slides: Presentation Slides")
expect(capture).to_contain("draw: SDD Diagram Draw")
expect(capture).to_contain("sheets: Spreadsheet")
expect(capture).to_contain("db-admin: Database Admin")
expect(capture).to_contain("  tui: tui-panels:")
expect(_write_tui_capture(capture)).to_equal(0)
expect(_capture_file_state(capture)).to_equal("matched")
```

</details>

#### keeps GUI and TUI feature-check probes in parity except launch mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tui_lines = ide_feature_check_report("tui")
val gui_lines = ide_feature_check_report("gui")
expect(tui_lines.len()).to_equal(gui_lines.len())
expect(tui_lines[0]).to_equal(gui_lines[0])
expect(tui_lines[2]).to_equal(gui_lines[2])
expect(tui_lines[3]).to_equal(gui_lines[3])
expect(tui_lines[5]).to_equal(gui_lines[5])
expect(tui_lines[6]).to_equal(gui_lines[6])
expect(tui_lines[8]).to_equal(gui_lines[8])
expect(tui_lines[10]).to_equal(gui_lines[10])
expect(tui_lines[12]).to_equal(gui_lines[12])
expect(tui_lines[14]).to_equal(gui_lines[14])
expect(tui_lines[18]).to_equal(gui_lines[18])
expect(tui_lines[20]).to_equal(gui_lines[20])
expect(tui_lines[22]).to_equal(gui_lines[22])
expect(tui_lines[23]).to_equal(gui_lines[23])
```

</details>

#### reports Draw SDD capability through a pure IDE sanity probe

<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_draw_sanity_probe()
expect(probe.owner_module).to_equal("std.editor.services.sdn_graph")
expect(probe.node_count).to_equal(3)
expect(probe.edge_count).to_equal(2)
expect(probe.html_render).to_be(true)
expect(probe.selected_render).to_be(true)
expect(probe.node_create).to_be(true)
expect(probe.style_rule_edit).to_be(true)
expect(probe.style_rule_delete).to_be(true)
expect(probe.style_rule_inspect).to_be(true)
expect(probe.edge_create).to_be(true)
expect(probe.edge_duplicate).to_be(true)
expect(probe.edge_label_point_edit).to_be(true)
expect(probe.reroute_edit).to_be(true)
expect(probe.node_edit).to_be(true)
expect(probe.node_geometry_edit).to_be(true)
expect(probe.node_layer_edit).to_be(true)
expect(probe.node_order_edit).to_be(true)
expect(probe.node_role_edit).to_be(true)
expect(probe.edge_style_edit).to_be(true)
expect(probe.edge_kind_edit).to_be(true)
expect(probe.reconnect_edit).to_be(true)
expect(probe.delete_edit).to_be(true)
expect(probe.node_delete_edit).to_be(true)
expect(probe.inspector).to_be(true)
expect(probe.group_child_metadata).to_be(true)
expect(probe.connector_path_metadata).to_be(true)
expect(probe.layout_edit).to_be(true)
expect(probe.canvas_metadata).to_be(true)
expect(ide_draw_sanity_summary()).to_contain("path_meta=true")
expect(ide_draw_sanity_summary()).to_contain("child_meta=true")
expect(ide_draw_sanity_summary()).to_contain("format=sdd")
expect(ide_draw_sanity_summary()).to_contain("name=\"SDD: Simple Diagram Document\"")
expect(ide_draw_sanity_summary()).to_contain("extension=.sdd.sdn")
expect(ide_draw_sanity_summary()).to_contain("layout=true")
expect(ide_draw_sanity_summary()).to_contain("geometry=true")
expect(ide_draw_sanity_summary()).to_contain("layer=true")
expect(ide_draw_sanity_summary()).to_contain("order=true")
expect(ide_draw_sanity_summary()).to_contain("role=true")
expect(ide_draw_sanity_summary()).to_contain("node_create=true")
expect(ide_draw_sanity_summary()).to_contain("style_rule=true")
expect(ide_draw_sanity_summary()).to_contain("style_delete=true")
expect(ide_draw_sanity_summary()).to_contain("style_inspect=true")
expect(ide_draw_sanity_summary()).to_contain("edge_create=true")
expect(ide_draw_sanity_summary()).to_contain("edge_duplicate=true")
expect(ide_draw_sanity_summary()).to_contain("edge_label_point=true")
expect(ide_draw_sanity_summary()).to_contain("edge_style=true")
expect(ide_draw_sanity_summary()).to_contain("edge_kind=true")
expect(ide_draw_sanity_summary()).to_contain("reconnect=true")
expect(ide_draw_sanity_summary()).to_contain("delete=true")
expect(ide_draw_sanity_summary()).to_contain("node_delete=true")
expect(ide_draw_sanity_summary()).to_contain("canvas=true")
```

</details>

#### exposes a complete LLM-readable app feature catalog

- var base table = new table
- base table = insert row checked
   - Expected: updated_base.affected_count equals `2`
   - Expected: count_where(updated_base.table, "status", "done") equals `2`
   - Expected: row_count(deleted_base.table) equals `0`
   - Expected: math_bad_action.reason equals `syntax-error`
   - Expected: math_to_mathml_checked("a +").reason equals `syntax-error`
   - Expected: counter_inc_action.reason equals `incremented`
   - Expected: counter_bad_action.reason equals `unsupported`
   - Expected: counter_overflow_action.reason equals `invalid-args`


<details>
<summary>Executable SSpec</summary>

Runnable source: 617 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = office_llm_feature_catalog()
val names = office_llm_catalog_app_names().join(",")
expect(catalog.len()).to_equal(9)
expect(names).to_equal("Markdown,Writer,Calc,Impress,Draw,Designer,Base,Math,Counter")
expect(office_llm_catalog_is_valid()).to_be(true)
expect(office_llm_catalog_summary()).to_equal("llm-catalog: apps=9 features=97 actions=56")
val dispatch_probe = office_catalog_dispatch_probe()
expect(dispatch_probe.advertised_count).to_equal(56)
expect(dispatch_probe.recognized_count).to_equal(56)
expect(dispatch_probe.missing_actions.len()).to_equal(0)

expect(catalog[0].owner_module).to_equal("app.office.md_wysiwyg")
expect(catalog[0].features.join(",")).to_contain("html-render")
expect(catalog[0].features.join(",")).to_contain("guarded-edit")
expect(catalog[0].actions.join(",")).to_contain("render-markdown-preview-html")
expect(catalog[0].actions.join(",")).to_contain("md-edit")
expect(catalog[1].features.join(",")).to_contain("markdown-source")
expect(catalog[1].actions.join(",")).to_contain("render-writer-markdown-html")
expect(catalog[2].owner_module).to_equal("app.office.sheets")
expect(catalog[2].features.join(",")).to_contain("formulas")
expect(catalog[2].features.join(",")).to_contain("formula-counta")
expect(catalog[2].features.join(",")).to_contain("formula-text-functions")
expect(catalog[2].features.join(",")).to_contain("formula-vlookup")
expect(catalog[2].features.join(",")).to_contain("formula-display-recalc")
expect(catalog[2].actions.join(",")).to_contain("sheet-edit")
expect(catalog[3].owner_module).to_equal("app.office.slides")
expect(catalog[3].features.join(",")).to_contain("markdown-source")
expect(catalog[3].features.join(",")).to_contain("css-like-design")
expect(catalog[3].actions.join(",")).to_contain("render-ppt-markdown-html")
expect(catalog[3].actions.join(",")).to_contain("slide-edit")
expect(catalog[4].owner_module).to_equal("std.editor.services.sdn_graph")
expect(catalog[4].features.join(",")).to_contain("sdd-source")
expect(catalog[4].features.join(",")).to_contain("connector-paths")
expect(catalog[4].features.join(",")).to_contain("group-containers")
expect(catalog[4].features.join(",")).to_contain("style-rule-edit")
expect(catalog[4].features.join(",")).to_contain("style-rule-delete")
expect(catalog[4].features.join(",")).to_contain("style-rule-inspector")
expect(catalog[4].features.join(",")).to_contain("node-create")
expect(catalog[4].features.join(",")).to_contain("node-label-edit")
expect(catalog[4].features.join(",")).to_contain("node-geometry-edit")
expect(catalog[4].features.join(",")).to_contain("node-delete")
expect(catalog[4].features.join(",")).to_contain("edge-create")
expect(catalog[4].features.join(",")).to_contain("edge-duplicate")
expect(catalog[4].features.join(",")).to_contain("edge-label-edit")
expect(catalog[4].features.join(",")).to_contain("edge-style-edit")
expect(catalog[4].features.join(",")).to_contain("edge-kind-edit")
expect(catalog[4].features.join(",")).to_contain("edge-reconnect-edit")
expect(catalog[4].features.join(",")).to_contain("edge-delete")
expect(catalog[4].features.join(",")).to_contain("node-shape-edit")
expect(catalog[4].features.join(",")).to_contain("node-style-edit")
expect(catalog[4].features.join(",")).to_contain("node-layer-edit")
expect(catalog[4].features.join(",")).to_contain("node-order-edit")
expect(catalog[4].features.join(",")).to_contain("node-role-edit")
expect(catalog[4].features.join(",")).to_contain("node-duplicate")
expect(catalog[4].features.join(",")).to_contain("canvas-metadata")
expect(catalog[4].features.join(",")).to_contain("selection")
expect(catalog[4].features.join(",")).to_contain("inspector")
expect(catalog[4].features.join(",")).to_contain("align-layout")
expect(catalog[4].features.join(",")).to_contain("distribute-layout")
expect(catalog[4].actions.join(",")).to_contain("render-sdd-html-with-selection")
expect(catalog[4].actions.join(",")).to_contain("reroute-sdd-connector")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-style-rule")
expect(catalog[4].actions.join(",")).to_contain("delete-sdd-style-rule")
expect(catalog[4].actions.join(",")).to_contain("inspect-sdd-style-rule")
expect(catalog[4].actions.join(",")).to_contain("add-sdd-node")
expect(catalog[4].actions.join(",")).to_contain("add-sdd-edge")
expect(catalog[4].actions.join(",")).to_contain("duplicate-sdd-edge")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-edge-label")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-edge-style")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-edge-kind")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-edge-endpoints")
expect(catalog[4].actions.join(",")).to_contain("delete-sdd-edge")
expect(catalog[4].actions.join(",")).to_contain("delete-sdd-node")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-node-label")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-node-geometry")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-node-parent")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-node-shape")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-node-style")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-node-layer")
expect(catalog[4].actions.join(",")).to_contain("order-sdd-node")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-node-role")
expect(catalog[4].actions.join(",")).to_contain("duplicate-sdd-node")
expect(catalog[4].actions.join(",")).to_contain("edit-sdd-canvas")
expect(catalog[4].actions.join(",")).to_contain("align-sdd-selection")
expect(catalog[4].actions.join(",")).to_contain("distribute-sdd-selection")
expect(catalog[4].actions.join(",")).to_contain("inspect-sdd-node")
expect(catalog[4].actions.join(",")).to_contain("inspect-sdd-edge")
val md_action = office_action_dispatch("render-markdown-preview-html", "# Markdown")
val md_edit_action = office_action_dispatch("md-edit", "1|old|new\n# Markdown\nold")
val md_code_edit_action = office_action_dispatch("md-edit", "1|print(1)|print(2)\n```simple\nprint(1)\n```")
val md_stale_edit_action = office_action_dispatch("md-edit", "1|missing|new\n# Markdown\nold")
val writer_action = office_action_dispatch("render-writer-markdown-html", "# Writer")
val ppt_action = office_action_dispatch("render-ppt-markdown-html", "# Deck\n\n## Slide")
val sheet_edit_action = office_action_dispatch("sheet-edit", "A1|old|new\nA1=old")
val sheet_stale_edit_action = office_action_dispatch("sheet-edit", "A1|missing|new\nA1=old")
val sheet_duplicate_source_action = office_action_dispatch("sheet-edit", "A1|new|next\nA1=old;A01=new")
val sheet_blank_target_action = office_action_dispatch("sheet-edit", "   |old|new\nA1=old")
val slide_edit_action = office_action_dispatch("slide-edit", "title|Old|New\ntitle=Old")
val slide_stale_edit_action = office_action_dispatch("slide-edit", "title|Missing|New\ntitle=Old")
val slide_duplicate_source_action = office_action_dispatch("slide-edit", "title|New|Next\ntitle=Old;title=New")
val slide_blank_target_action = office_action_dispatch("slide-edit", "   |Old|New\ntitle=Old")
val ui_action = office_action_dispatch("render-ui-html", "design: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val ui_sdd_action = office_action_dispatch("export-ui-sdd", "design: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val sdd_action = office_action_dispatch("render-sdd-html-with-selection", "graph: Feature\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val legacy_ui_action = office_action_dispatch("ui-render", "design: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val legacy_ui_sdd_action = office_action_dispatch("ui-export-sdd", "design: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val legacy_sdd_action = office_action_dispatch("render-sdd", "graph: Feature\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val ui_duplicate_action = office_action_dispatch("ui-duplicate-node", "button|button_copy|20|10\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_ui_duplicate_action = office_action_dispatch("ui-duplicate-node", "   |button_copy|20|10\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_offset_ui_duplicate_action = office_action_dispatch("ui-duplicate-node", "button|button_copy|   |10\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val ui_label_action = office_action_dispatch("ui-label-edit", "button|Run|Launch\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val stale_ui_label_action = office_action_dispatch("ui-label-edit", "button|Old|Launch\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_ui_label_action = office_action_dispatch("ui-label-edit", "   |Run|Launch\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val ui_layout_action = office_action_dispatch("ui-layout-edit", "button|16|16|80|32|24|32|96|40\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_ui_layout_action = office_action_dispatch("ui-layout-edit", "   |16|16|80|32|24|32|96|40\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_geometry_ui_layout_action = office_action_dispatch("ui-layout-edit", "button|16|16|80|32|   |32|96|40\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val ui_auto_layout_action = office_action_dispatch("ui-auto-layout-edit", "frame|off|0|0,0,0,0|vertical|8|4,4,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container\nnode button|Run|button|16|16|80|32|primary|frame|action")
val blank_ui_auto_layout_action = office_action_dispatch("ui-auto-layout-edit", "   |off|0|0,0,0,0|vertical|8|4,4,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container")
val blank_field_ui_auto_layout_action = office_action_dispatch("ui-auto-layout-edit", "frame|off|   |0,0,0,0|vertical|8|4,4,4,4\ndesign: Feature\nnode frame|Panel|frame|0|0|200|120|surface|1|container")
val ui_constraints_action = office_action_dispatch("ui-constraints-edit", "button|left|top|stretch|top\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_ui_constraints_action = office_action_dispatch("ui-constraints-edit", "   |left|top|stretch|top\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_field_ui_constraints_action = office_action_dispatch("ui-constraints-edit", "button|left|top|   |top\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val ui_layer_action = office_action_dispatch("ui-layer-edit", "button|controls|9\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_ui_layer_action = office_action_dispatch("ui-layer-edit", "   |controls|9\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val ui_style_read_action = office_action_dispatch("ui-style-token-read", "button\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val ui_style_edit_action = office_action_dispatch("ui-style-token-edit", "button|primary|accent\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val blank_ui_style_edit_action = office_action_dispatch("ui-style-token-edit", "   |primary|accent\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val ui_inspect_action = office_action_dispatch("ui-inspect-node", "button\ndesign: Feature\nnode button|Run|button|16|16|80|32|primary|controls|action")
val sdd_duplicate_action = office_action_dispatch("duplicate-sdd-node", "A|A_copy|20|10\ngraph: Feature\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val blank_sdd_duplicate_action = office_action_dispatch("duplicate-sdd-node", "A|   |20|10\ngraph: Feature\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val sdd_style_rule_action = office_action_dispatch("edit-sdd-style-rule", "accent|node|none|fill|#eeeeee\ngraph: Style Rule\nA: Alpha @accent x: 0 y: 0 width: 80 height: 20")
val sdd_style_rule_delete_action = office_action_dispatch("delete-sdd-style-rule", "accent|fill\n" + sdd_style_rule_action.output)
val sdd_style_rule_inspect_action = office_action_dispatch("inspect-sdd-style-rule", "accent|fill\ncss |name, extends, target|\n    accent, none, node\nstyles |css, key, value|\n    accent, fill, #eeeeee")
val deleted_sdd_style_rule_inspect_action = office_action_dispatch("inspect-sdd-style-rule", "accent|fill\n" + sdd_style_rule_delete_action.output)
val missing_sdd_style_rule_inspect_action = office_action_dispatch("inspect-sdd-style-rule", "accent|stroke\ncss |name, extends, target|\n    accent, none, node\nstyles |css, key, value|\n    accent, fill, #eeeeee")
val blank_sdd_style_rule_inspect_action = office_action_dispatch("inspect-sdd-style-rule", "accent|   \ncss |name, extends, target|\n    accent, none, node\nstyles |css, key, value|\n    accent, fill, #eeeeee")
val blank_sdd_style_rule_delete_action = office_action_dispatch("delete-sdd-style-rule", "accent|   \n" + sdd_style_rule_action.output)
val blank_sdd_style_rule_edit_action = office_action_dispatch("edit-sdd-style-rule", "accent|node|none|   |#eeeeee\ngraph: Style Rule\nA: Alpha @accent")
val invalid_sdd_style_rule_action = office_action_dispatch("edit-sdd-style-rule", "accent|canvas|none|fill|#eeeeee\ngraph: Style Rule\nA: Alpha @accent")
val invalid_sdd_style_token_action = office_action_dispatch("edit-sdd-style-rule", "accent,bad|node|none|fill|#eeeeee\ngraph: Style Rule\nA: Alpha @accent")
val self_parent_sdd_style_rule_action = office_action_dispatch("edit-sdd-style-rule", "accent|node|accent|fill|#eeeeee\ngraph: Style Rule\nA: Alpha @accent")
val indirect_parent_sdd_style_rule_action = office_action_dispatch("edit-sdd-style-rule", "accent|node|base|fill|#eeeeee\ngraph: Style Rule\ncss base:\n    extends: accent\nA: Alpha @accent")
val missing_sdd_style_rule_delete_action = office_action_dispatch("delete-sdd-style-rule", "accent|stroke\n" + sdd_style_rule_action.output)
val sdd_add_node_action = office_action_dispatch("add-sdd-node", "C|Choice|accent|decision|diamond|80|64|48|32|front|A\ngraph: Node Add\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val duplicate_sdd_add_node_action = office_action_dispatch("add-sdd-node", "A|Again|accent|decision|diamond|80|64|48|32|front|\ngraph: Node Add\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val invalid_sdd_add_node_action = office_action_dispatch("add-sdd-node", "|Blank|accent|decision|diamond|80|64|48|32|front|\ngraph: Node Add\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val blank_geometry_sdd_add_node_action = office_action_dispatch("add-sdd-node", "C|Choice|accent|decision|diamond|   |64|48|32|front|\ngraph: Node Add\nA: Alpha")
val self_parent_sdd_add_node_action = office_action_dispatch("add-sdd-node", "C|Choice|accent|decision|diamond|80|64|48|32|front|C\ngraph: Node Add\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val blank_offset_sdd_duplicate_action = office_action_dispatch("duplicate-sdd-node", "A|A_copy|   |10\ngraph: Feature\nA: Alpha x: 0 y: 0 width: 80 height: 20")
val ui_align_action = office_action_dispatch("ui-align-selection", "left|a,b\ndesign: Align\nnode a|A|button|0|0|20|20|primary|1|action\nnode b|B|button|40|20|20|20|secondary|2|action")
val sdd_align_action = office_action_dispatch("align-sdd-selection", "left|A,B\ngraph: Align\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 40 y: 20 width: 20 height: 20")
val blank_ui_align_action = office_action_dispatch("ui-align-selection", "left| , , \ndesign: Align\nnode a|A|button|0|0|20|20|primary|1|action")
val blank_sdd_align_action = office_action_dispatch("align-sdd-selection", "   |A\ngraph: Align\nA: A x: 0 y: 0 width: 20 height: 20")
val ui_distribute_action = office_action_dispatch("ui-distribute-selection", "horizontal|a,b,c\ndesign: Dist\nnode a|A|button|0|0|20|20|primary|1|action\nnode b|B|button|40|0|20|20|secondary|2|action\nnode c|C|button|100|0|20|20|ghost|3|action")
val sdd_distribute_action = office_action_dispatch("distribute-sdd-selection", "horizontal|A,B,C\ngraph: Dist\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 40 y: 0 width: 20 height: 20\nC: C x: 100 y: 0 width: 20 height: 20")
val sdd_shape_action = office_action_dispatch("edit-sdd-node-shape", "A|diamond\ngraph: Shape\nA: A x: 0 y: 0 width: 20 height: 20")
val sdd_style_action = office_action_dispatch("edit-sdd-node-style", "A|accent\ngraph: Style\nA: A x: 0 y: 0 width: 20 height: 20")
val blank_sdd_style_action = office_action_dispatch("edit-sdd-node-style", "   |accent\ngraph: Style\nA: A x: 0 y: 0 width: 20 height: 20")
val invalid_sdd_shape_action = office_action_dispatch("edit-sdd-node-shape", "A|bad shape\ngraph: Shape\nA: A x: 0 y: 0 width: 20 height: 20")
val invalid_sdd_style_action = office_action_dispatch("edit-sdd-node-style", "A|accent,bad\ngraph: Style\nA: A x: 0 y: 0 width: 20 height: 20")
val sdd_label_action = office_action_dispatch("edit-sdd-node-label", "A|Renamed\ngraph: Label\nA: Old x: 0 y: 0 width: 20 height: 20")
val missing_sdd_label_action = office_action_dispatch("edit-sdd-node-label", "Nope|Renamed\ngraph: Label\nA: Old x: 0 y: 0 width: 20 height: 20")
val sdd_geometry_action = office_action_dispatch("edit-sdd-node-geometry", "A|-8|12|64|32\ngraph: Geometry\nA: Old @accent role: actor shape: diamond x: 0 y: 0 width: 20 height: 20 layer: front")
val invalid_sdd_geometry_action = office_action_dispatch("edit-sdd-node-geometry", "A|0|0|-1|32\ngraph: Geometry\nA: Old x: 0 y: 0 width: 20 height: 20")
val blank_sdd_geometry_action = office_action_dispatch("edit-sdd-node-geometry", "   |0|0|20|20\ngraph: Geometry\nA: A x: 0 y: 0 width: 20 height: 20")
val sdd_layer_action = office_action_dispatch("edit-sdd-node-layer", "A|front\ngraph: Layer\nA: Old x: 0 y: 0 width: 20 height: 20 layer: back")
val invalid_sdd_layer_action = office_action_dispatch("edit-sdd-node-layer", "A|front layer\ngraph: Layer\nA: Old x: 0 y: 0 width: 20 height: 20 layer: back")
val sdd_order_action = office_action_dispatch("order-sdd-node", "A|front\ngraph: Order\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 40 y: 0 width: 20 height: 20")
val blank_sdd_order_action = office_action_dispatch("order-sdd-node", "   |front\ngraph: Order\nA: A\nB: B")
val invalid_sdd_order_action = office_action_dispatch("order-sdd-node", "A|middle\ngraph: Order\nA: A\nB: B")
val sdd_role_action = office_action_dispatch("edit-sdd-node-role", "A|database\ngraph: Role\nA: Old role: actor x: 0 y: 0 width: 20 height: 20")
val invalid_sdd_role_action = office_action_dispatch("edit-sdd-node-role", "A|data base\ngraph: Role\nA: Old role: actor x: 0 y: 0 width: 20 height: 20")
val stale_sdd_geometry_action = office_action_dispatch("edit-sdd-node-geometry", "Nope|0|0|10|10\ngraph: Geometry\nA: A")
val sdd_parent_action = office_action_dispatch("edit-sdd-node-parent", "B|A\ngraph: Parent\nA: A x: 0 y: 0 width: 80 height: 80\nB: B x: 10 y: 10 width: 20 height: 20")
val sdd_parent_cycle_action = office_action_dispatch("edit-sdd-node-parent", "A|B\ngraph: Parent Cycle\nA: A x: 0 y: 0 width: 80 height: 80\nB: B x: 10 y: 10 width: 20 height: 20 parent: A")
val sdd_node_delete_action = office_action_dispatch("delete-sdd-node", "B\ngraph: Node Delete\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val missing_sdd_node_delete_action = office_action_dispatch("delete-sdd-node", "Nope\ngraph: Node Delete\nA: A")
val sdd_canvas_action = office_action_dispatch("edit-sdd-canvas", "640|480|16|true|125|#ffffff\ngraph: Canvas\nA: A")
val invalid_sdd_canvas_action = office_action_dispatch("edit-sdd-canvas", "640|480|16;bad|true|125|#ffffff\ngraph: Canvas\nA: A")
val blank_sdd_canvas_action = office_action_dispatch("edit-sdd-canvas", "640|480|16|true|125|   \ngraph: Canvas\nA: A")
val sdd_reroute_action = office_action_dispatch("reroute-sdd-connector", "0|orthogonal|60x10;60x40|right|left\ngraph: Route\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val invalid_sdd_reroute_action = office_action_dispatch("reroute-sdd-connector", "0|curve|60x10|right|left\ngraph: Route\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val sdd_add_edge_action = office_action_dispatch("add-sdd-edge", "B|A|return|secondary|reply|simple||left|right\ngraph: Edge Add\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20")
val sdd_duplicate_edge_action = office_action_dispatch("duplicate-sdd-edge", "0\ngraph: Edge Copy\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: flow @primary route: simple start: right end: left")
val invalid_sdd_add_edge_action = office_action_dispatch("add-sdd-edge", "B|A|return|secondary|reply|curve||left|right\ngraph: Edge Add\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20")
val blank_sdd_add_edge_action = office_action_dispatch("add-sdd-edge", "   |A|return|secondary|reply|simple||left|right\ngraph: Edge Add\nA: A x: 0 y: 0 width: 20 height: 20")
val missing_sdd_add_edge_action = office_action_dispatch("add-sdd-edge", "B|Nope|return|secondary|reply|simple||left|right\ngraph: Edge Add\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20")
val missing_sdd_duplicate_edge_action = office_action_dispatch("duplicate-sdd-edge", "8\ngraph: Edge Copy\nA: A\nB: B\nA -> B: flow")
val sdd_edge_label_action = office_action_dispatch("edit-sdd-edge-label", "0|approved\ngraph: Edge Label\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val sdd_edge_label_point_action = office_action_dispatch("edit-sdd-edge-label-point", "0|66|12\ngraph: Edge Label Point\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val blank_sdd_edge_label_point_action = office_action_dispatch("edit-sdd-edge-label-point", "0|   |12\ngraph: Edge Label Point\nA: A\nB: B\nA -> B: link")
val sdd_edge_style_action = office_action_dispatch("edit-sdd-edge-style", "0|warning dashed\ngraph: Edge Style\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val invalid_sdd_edge_style_action = office_action_dispatch("edit-sdd-edge-style", "0|warning,bad\ngraph: Edge Style\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val sdd_edge_kind_action = office_action_dispatch("edit-sdd-edge-kind", "0|async\ngraph: Edge Kind\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link kind: request route: simple start: right end: left")
val invalid_sdd_edge_kind_action = office_action_dispatch("edit-sdd-edge-kind", "0|async bad\ngraph: Edge Kind\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link kind: request route: simple start: right end: left")
val sdd_edge_endpoints_action = office_action_dispatch("edit-sdd-edge-endpoints", "0|B|A\ngraph: Edge Endpoints\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val blank_sdd_edge_endpoint_action = office_action_dispatch("edit-sdd-edge-endpoints", "0|B|   \ngraph: Edge Endpoints\nA: A\nB: B\nA -> B: link")
val missing_sdd_edge_endpoint_index_action = office_action_dispatch("edit-sdd-edge-endpoints", "1|B|A\ngraph: Edge Endpoints\nA: A\nB: B\nA -> B: link")
val sdd_edge_delete_action = office_action_dispatch("delete-sdd-edge", "0\ngraph: Edge Delete\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 100 y: 0 width: 20 height: 20\nA -> B: link route: simple start: right end: left")
val missing_sdd_edge_label_action = office_action_dispatch("edit-sdd-edge-label", "1|approved\ngraph: Edge Label\nA: A\nB: B\nA -> B: link")
val invalid_sdd_edge_label_point_action = office_action_dispatch("edit-sdd-edge-label-point", "0|bad\"x|12\ngraph: Edge Label Point\nA: A\nB: B\nA -> B: link")
val missing_sdd_edge_style_action = office_action_dispatch("edit-sdd-edge-style", "1|warning\ngraph: Edge Style\nA: A\nB: B\nA -> B: link")
val missing_sdd_edge_endpoint_action = office_action_dispatch("edit-sdd-edge-endpoints", "0|A|Nope\ngraph: Edge Endpoints\nA: A\nB: B\nA -> B: link")
val missing_sdd_edge_delete_action = office_action_dispatch("delete-sdd-edge", "1\ngraph: Edge Delete\nA: A\nB: B\nA -> B: link")
val missing_sdd_edge_action = office_action_dispatch("reroute-sdd-connector", "1|orthogonal|60x10|right|left\ngraph: Route\nA: A\nB: B\nA -> B: link")
val sdd_inspect_node_action = office_action_dispatch("inspect-sdd-node", "A\ngraph: Inspect\nA: Alpha @accent role: actor shape: diamond x: 4 y: 8 width: 80 height: 24 layer: front\nB: Beta x: 12 y: 16 width: 20 height: 10 parent: A")
val sdd_inspect_edge_action = office_action_dispatch("inspect-sdd-edge", "0\ngraph: Inspect\nA: A x: 0 y: 0 width: 20 height: 20\nB: B x: 80 y: 0 width: 20 height: 20\nA -> B: link route: orthogonal waypoints: 40x10 start: right end: left")
val missing_sdd_inspect_edge_action = office_action_dispatch("inspect-sdd-edge", "1\ngraph: Inspect\nA: A\nB: B\nA -> B: link")
expect(md_action.output).to_contain("class=\"wysiwyg-preview\"")
expect(md_action.output).to_contain("data-format=\"markdown-wysiwyg\"")
expect(md_action.output).to_contain("data-line-count=\"1\"")
expect(md_action.output).to_contain("data-line-no=\"0\"")
expect(md_action.output).to_contain("<h1>Markdown</h1>")
expect(md_edit_action.output).to_contain("new")
expect(md_edit_action.reason).to_equal("updated")
expect(md_code_edit_action.output).to_contain("<pre")
expect(md_code_edit_action.output).to_contain(">print(2)</pre>")
expect(md_stale_edit_action.reason).to_equal("stale-line")
expect(writer_action.output).to_contain("class=\"md-paper\"")
expect(writer_action.output).to_contain("data-format=\"markdown-paper\"")
expect(ppt_action.output).to_contain("class=\"md-ppt-deck\"")
expect(ppt_action.output).to_contain("data-format=\"markdown-ppt\"")
expect(sheet_edit_action.output).to_equal("A1=new")
expect(sheet_edit_action.reason).to_equal("updated")
expect(sheet_duplicate_source_action.reason).to_equal("duplicate-source-ref")
expect(sheet_blank_target_action.reason).to_equal("invalid-args")
expect(sheet_stale_edit_action.reason).to_equal("stale-cell")
expect(slide_edit_action.output).to_equal("title=New")
expect(slide_edit_action.reason).to_equal("updated")
expect(slide_duplicate_source_action.reason).to_equal("duplicate-source-id")
expect(slide_blank_target_action.reason).to_equal("invalid-args")
expect(slide_stale_edit_action.reason).to_equal("stale-slide-element")
expect(ui_action.output).to_contain("data-format=\"html-ui\"")
expect(ui_action.output).to_contain("data-node-count=\"1\"")
expect(ui_sdd_action.output).to_contain("nodes |id, label, css, role, shape")
expect(sdd_action.output).to_contain("class=\"sdn-graph sdd-diagram\"")
expect(sdd_action.output).to_contain("data-node-count=\"1\"")
expect(sdd_action.output).to_contain("data-edge-count=\"0\"")
expect(legacy_ui_action.action).to_equal("render-ui-html")
expect(legacy_ui_action.output).to_contain("data-format=\"html-ui\"")
expect(legacy_ui_sdd_action.action).to_equal("export-ui-sdd")
expect(legacy_ui_sdd_action.output).to_contain("nodes |id, label, css, role, shape")
expect(legacy_sdd_action.action).to_equal("render-sdd-html")
expect(legacy_sdd_action.output).to_contain("class=\"sdn-graph sdd-diagram\"")
expect(sdd_action.output).to_contain("data-selected-edge-index=\"-1\"")
expect(ui_duplicate_action.output).to_contain("data-id=\"button_copy\"")
expect(blank_ui_duplicate_action.reason).to_equal("invalid-args")
expect(blank_offset_ui_duplicate_action.reason).to_equal("invalid-args")
expect(ui_label_action.output).to_contain(">Launch</div>")
expect(stale_ui_label_action.reason).to_equal("stale-node")
expect(blank_ui_label_action.reason).to_equal("invalid-args")
expect(ui_layout_action.output).to_contain("left: 24px")
expect(blank_ui_layout_action.reason).to_equal("invalid-args")
expect(blank_geometry_ui_layout_action.reason).to_equal("invalid-args")
expect(ui_auto_layout_action.output).to_contain("data-layout-mode=\"vertical\"")
expect(blank_ui_auto_layout_action.reason).to_equal("invalid-args")
expect(blank_field_ui_auto_layout_action.reason).to_equal("invalid-args")
expect(ui_constraints_action.output).to_contain("data-constraint-h=\"stretch\"")
expect(blank_ui_constraints_action.reason).to_equal("invalid-args")
expect(blank_field_ui_constraints_action.reason).to_equal("invalid-args")
expect(ui_layer_action.output).to_contain("data-z-index=\"9\"")
expect(blank_ui_layer_action.reason).to_equal("invalid-args")
expect(ui_style_read_action.output).to_equal("primary")
expect(ui_style_edit_action.output).to_contain("office-ui-css-accent")
expect(blank_ui_style_edit_action.reason).to_equal("invalid-args")
expect(ui_inspect_action.output).to_contain("z_index=0")
expect(ui_inspect_action.output).to_contain("x=16")
expect(ui_inspect_action.output).to_contain("component=action")
expect(sdd_duplicate_action.output).to_contain("data-node=\"A_copy\"")
expect(blank_sdd_duplicate_action.reason).to_equal("invalid-args")
expect(sdd_style_rule_action.output).to_contain("css |name, extends, target|")
expect(sdd_style_rule_action.output).to_contain("accent, fill, #eeeeee")
expect(sdn_graph_render_html(sdn_graph_parse(sdd_style_rule_action.output))).to_contain("background-color:#eeeeee")
expect(sdd_style_rule_delete_action.reason).to_equal("updated")
expect(deleted_sdd_style_rule_inspect_action.reason).to_equal("missing-style-rule")
expect(sdd_style_rule_inspect_action.output).to_contain("value=#eeeeee")
expect(sdd_style_rule_inspect_action.output).to_contain("target=node")
expect(missing_sdd_style_rule_inspect_action.reason).to_equal("missing-style-rule")
expect(missing_sdd_style_rule_delete_action.reason).to_equal("missing-style-rule")
expect(blank_sdd_style_rule_inspect_action.reason).to_equal("invalid-args")
expect(blank_sdd_style_rule_delete_action.reason).to_equal("invalid-args")
expect(blank_sdd_style_rule_edit_action.reason).to_equal("invalid-args")
expect(invalid_sdd_style_rule_action.reason).to_equal("invalid-target")
expect(invalid_sdd_style_token_action.reason).to_equal("invalid-style-token")
expect(self_parent_sdd_style_rule_action.reason).to_equal("style-parent-cycle")
expect(indirect_parent_sdd_style_rule_action.reason).to_equal("style-parent-cycle")
expect(sdd_add_node_action.output).to_contain("data-node=\"C\"")
expect(sdd_add_node_action.output).to_contain("data-shape=\"diamond\"")
expect(sdd_add_node_action.output).to_contain("data-parent=\"A\"")
expect(duplicate_sdd_add_node_action.reason).to_equal("duplicate-id")
expect(invalid_sdd_add_node_action.reason).to_equal("invalid-id")
expect(blank_geometry_sdd_add_node_action.reason).to_equal("invalid-args")
expect(self_parent_sdd_add_node_action.reason).to_equal("missing-parent")
expect(blank_offset_sdd_duplicate_action.reason).to_equal("invalid-args")
expect(ui_align_action.output).to_contain("data-id=\"b\"")
expect(ui_align_action.output).to_contain("left: 0px")
expect(sdd_align_action.output).to_contain("data-node=\"B\"")
expect(sdd_align_action.output).to_contain("style=\"left:0px")
expect(blank_ui_align_action.reason).to_equal("invalid-args")
expect(blank_sdd_align_action.reason).to_equal("invalid-args")
expect(ui_distribute_action.output).to_contain("left: 50px")
expect(sdd_distribute_action.output).to_contain("style=\"left:50px")
expect(sdd_shape_action.output).to_contain("data-shape=\"diamond\"")
expect(sdd_style_action.output).to_contain("sdn-css-accent")
expect(blank_sdd_style_action.reason).to_equal("invalid-args")
expect(invalid_sdd_shape_action.reason).to_equal("invalid-shape-token")
expect(invalid_sdd_style_action.reason).to_equal("invalid-style-token")
expect(sdd_label_action.output).to_contain(">Renamed</button>")
expect(missing_sdd_label_action.reason).to_equal("missing-node")
expect(sdd_geometry_action.output).to_contain("style=\"left:-8px;top:12px;width:64px;height:32px\"")
expect(invalid_sdd_geometry_action.reason).to_equal("invalid-args")
expect(blank_sdd_geometry_action.reason).to_equal("invalid-args")
expect(sdd_layer_action.output).to_contain("data-layer=\"front\"")
expect(invalid_sdd_layer_action.reason).to_equal("invalid-layer-token")
expect(sdd_order_action.output).to_contain("data-node=\"A\"")
expect(sdd_order_action.output.index_of("data-node=\"A\"")).to_be_greater_than(sdd_order_action.output.index_of("data-node=\"B\""))
expect(blank_sdd_order_action.reason).to_equal("invalid-args")
expect(invalid_sdd_order_action.reason).to_equal("invalid-position")
expect(sdd_role_action.output).to_contain("data-role=\"database\"")
expect(invalid_sdd_role_action.reason).to_equal("invalid-role-token")
expect(stale_sdd_geometry_action.reason).to_equal("missing-node")
expect(sdd_parent_action.output).to_contain("data-parent=\"A\"")
expect(sdd_parent_cycle_action.reason).to_equal("parent-cycle")
expect(sdd_inspect_node_action.output).to_contain("child_count=1")
expect(sdd_inspect_node_action.output).to_contain("child_bounds=12,16,32,26")
expect(sdd_node_delete_action.reason).to_equal("updated")
expect(sdd_node_delete_action.output).to_contain("data-node=\"A\"")
expect(missing_sdd_node_delete_action.reason).to_equal("missing-node")
expect(sdd_canvas_action.output).to_contain("data-canvas-width=\"640\"")
expect(invalid_sdd_canvas_action.reason).to_equal("invalid-canvas-number")
expect(blank_sdd_canvas_action.reason).to_equal("invalid-args")
expect(sdd_reroute_action.output).to_contain("data-route=\"orthogonal\"")
expect(invalid_sdd_reroute_action.reason).to_equal("invalid-route")
expect(sdd_add_edge_action.output).to_contain(">return</div>")
expect(sdd_add_edge_action.output).to_contain("data-kind=\"reply\"")
expect(sdd_duplicate_edge_action.reason).to_equal("updated")
expect(sdd_duplicate_edge_action.output).to_contain("data-edge-index=\"1\"")
expect(sdd_duplicate_edge_action.output).to_contain("sdn-css-primary")
expect(invalid_sdd_add_edge_action.reason).to_equal("invalid-route")
expect(blank_sdd_add_edge_action.reason).to_equal("invalid-args")
expect(missing_sdd_add_edge_action.reason).to_equal("missing-node")
expect(missing_sdd_duplicate_edge_action.reason).to_equal("missing-edge")
expect(sdd_edge_label_action.output).to_contain(">approved</div>")
expect(sdd_edge_label_point_action.output).to_contain("data-label-x=\"66\" data-label-y=\"12\"")
expect(blank_sdd_edge_label_point_action.reason).to_equal("invalid-args")
expect(invalid_sdd_edge_label_point_action.reason).to_equal("invalid-label-point")
expect(sdd_edge_style_action.output).to_contain("sdn-css-warning sdn-css-dashed")
expect(invalid_sdd_edge_style_action.reason).to_equal("invalid-style-token")
expect(sdd_edge_kind_action.output).to_contain("data-kind=\"async\"")
expect(invalid_sdd_edge_kind_action.reason).to_equal("invalid-kind-token")
expect(sdd_edge_endpoints_action.output).to_contain("data-from=\"B\" data-to=\"A\"")
expect(blank_sdd_edge_endpoint_action.reason).to_equal("invalid-args")
expect(missing_sdd_edge_endpoint_index_action.reason).to_equal("missing-edge")
expect(sdd_edge_delete_action.reason).to_equal("updated")
expect(sdd_edge_delete_action.output).to_contain("data-selected-edge-index=\"-1\"")
expect(missing_sdd_edge_label_action.reason).to_equal("missing-edge")
expect(missing_sdd_edge_style_action.reason).to_equal("missing-edge")
expect(missing_sdd_edge_endpoint_action.reason).to_equal("missing-node")
expect(missing_sdd_edge_delete_action.reason).to_equal("missing-edge")
expect(missing_sdd_edge_action.reason).to_equal("missing-edge")
expect(sdd_inspect_node_action.output).to_contain("shape=diamond")
expect(sdd_inspect_node_action.output).to_contain("x=4")
expect(sdd_inspect_edge_action.output).to_contain("route=orthogonal")
expect(sdd_inspect_edge_action.output).to_contain("path=M")
expect(sdd_inspect_edge_action.output).to_contain("path_bounds=20,10,80,10")
expect(sdd_inspect_edge_action.output).to_contain("segment_count=2")
expect(sdd_inspect_edge_action.output).to_contain("segments=20,10-40,10;40,10-80,10")
expect(sdd_inspect_edge_action.output).to_contain("segment_midpoints=30,10;60,10")
expect(sdd_inspect_edge_action.output).to_contain("segment_orientations=h;h")
expect(missing_sdd_inspect_edge_action.reason).to_equal("missing-edge")
val draw_graph = sdn_graph_parse("graph: Feature\ncanvas: width: 800 height: 600 grid: 10 snap: false zoom: 100 background: white\nA: A x: 0 y: 0 width: 80 height: 20\nB: B x: 160 y: 0 width: 80 height: 20\nA -> B: flow route: simple start: right end: left")
val style_ruled = sdn_graph_set_style_rule_checked(sdn_graph_parse("graph: Style\nA: A @accent x: 0 y: 0 width: 80 height: 20"), "accent", "node", "none", "fill", "#eeeeee")
val inspected_style_rule = sdn_graph_inspect_style_rule(style_ruled.graph, "accent", "fill")
val deleted_style_rule = sdn_graph_delete_style_rule_checked(style_ruled.graph, "accent", "fill")
val inspected_deleted_style_rule = sdn_graph_inspect_style_rule(deleted_style_rule.graph, "accent", "fill")
val node_added = sdn_graph_add_node_checked(draw_graph, "C", "Choice", "accent", "decision", "diamond", "80", "80", "64", "48", "front", "A")
val edge_added = sdn_graph_add_edge(node_added.graph, "B", "A", "return", "secondary", "reply", "simple", "", "left", "right")
val edge_duplicated = sdn_graph_duplicate_edge_checked(edge_added, 1)
val rerouted = sdn_graph_update_edge_at(edge_added, 0, "orthogonal", "120x10;120x40", "right", "left")
val edge_labeled = sdn_graph_update_edge_label_at(rerouted, 0, "approved")
val edge_label_pointed = sdn_graph_update_edge_label_point_at(edge_labeled, 0, "140", "32")
val edge_styled = sdn_graph_update_edge_style_at(edge_label_pointed, 0, "warning dashed")
val edge_kinded = sdn_graph_update_edge_kind_at(edge_styled, 0, "async")
val edge_reconnected = sdn_graph_update_edge_endpoints_at(edge_kinded, 0, "B", "A")
val edge_deleted = sdn_graph_delete_edge_at(edge_reconnected, 0)
val node_deleted = sdn_graph_delete_node_at(edge_styled, 1)
val shaped = sdn_graph_update_node_at(edge_styled, 0, "accent", "decision", "diamond", "12", "8", "96", "48", "front")
val grouped = sdn_graph_update_node_parent_at(shaped, 1, "A")
val draw_shape_only = sdn_graph_update_node_shape_at(grouped, 1, "cylinder")
val draw_style_only = sdn_graph_update_node_style_at(draw_shape_only, 1, "storage")
val draw_label_only = sdn_graph_update_node_label_at(draw_style_only, 1, "Storage")
val draw_layer_only = sdn_graph_update_node_layer_at(draw_label_only, 1, "front")
val draw_ordered = sdn_graph_reorder_node_checked(draw_layer_only, "A", "front")
val draw_role_only = sdn_graph_update_node_role_at(draw_layer_only, 1, "database")
val draw_canvas = sdn_graph_update_canvas(draw_role_only, "1440", "960", "24", "true", "150", "#f8fafc")
val inspected_draw_node = sdn_graph_inspect_node(draw_role_only, "B")
val inspected_draw_edge = sdn_graph_inspect_edge(draw_role_only, 0)
val draw_layout_graph = sdn_graph_parse("graph: Layout\nB: B x: 120 y: 120 width: 20 height: 20\nA: A x: 0 y: 0 width: 20 height: 20\nC: C x: 20 y: 20 width: 20 height: 20")
val draw_layout_ids = ["A", "B", "C"]
val draw_layout_signature = sdn_graph_geometry_signature(draw_layout_graph, draw_layout_ids)
val draw_aligned = sdn_graph_align_checked(draw_layout_graph, draw_layout_ids, draw_layout_signature, "left")
val draw_distributed = sdn_graph_distribute_checked(draw_layout_graph, draw_layout_ids, draw_layout_signature, "horizontal")
val draw_duplicate = sdn_graph_duplicate_node_checked(draw_role_only, "B", "B_copy", "24", "12")
expect(style_ruled.accepted).to_be(true)
expect(inspected_style_rule.value).to_equal("#eeeeee")
expect(sdn_graph_render_html(style_ruled.graph)).to_contain("background-color:#eeeeee")
expect(deleted_style_rule.accepted).to_be(true)
expect(inspected_deleted_style_rule.reason).to_equal("missing-style-rule")
expect(node_added.accepted).to_be(true)
expect(node_added.graph.nodes[2].id).to_equal("C")
expect(sdn_graph_render_html(node_added.graph)).to_contain("data-node=\"C\"")
expect(edge_added.edges.len()).to_equal(2)
expect(sdn_graph_render_html(edge_added)).to_contain(">return</div>")
expect(edge_duplicated.accepted).to_be(true)
expect(edge_duplicated.graph.edges[2].label).to_equal("return")
expect(sdn_graph_render_html(rerouted)).to_contain("data-path=\"M 80,10 L 120,10 L 120,40 L 160,40 L 160,10\"")
expect(sdn_graph_render_html(edge_labeled)).to_contain(">approved</div>")
expect(sdn_graph_render_html(edge_styled)).to_contain("sdn-css-warning sdn-css-dashed")
expect(sdn_graph_render_html(edge_kinded)).to_contain("data-kind=\"async\"")
expect(sdn_graph_render_html(edge_reconnected)).to_contain("data-from=\"B\" data-to=\"A\"")
expect(edge_deleted.edges.len()).to_equal(0)
expect(node_deleted.nodes.len()).to_equal(2)
expect(node_deleted.nodes[1].id).to_equal("C")
expect(node_deleted.edges.len()).to_equal(0)
expect(sdn_graph_render_html(grouped)).to_contain("data-shape=\"diamond\"")
expect(sdn_graph_render_html(grouped)).to_contain("clip-path:polygon(50% 0,100% 50%,50% 100%,0 50%)")
expect(sdn_graph_render_html(grouped)).to_contain("sdn-css-accent")
expect(sdn_graph_render_html(grouped)).to_contain("data-parent=\"A\"")
expect(sdn_graph_render_html(draw_style_only)).to_contain("data-shape=\"cylinder\"")
expect(sdn_graph_render_html(draw_style_only)).to_contain("border-radius:999px / 24px")
expect(sdn_graph_render_html(draw_style_only)).to_contain("box-shadow:inset 0 8px 0 rgba(15,23,42,0.08)")
expect(sdn_graph_render_html(draw_style_only)).to_contain("sdn-css-storage")
expect(draw_label_only.nodes[1].label).to_equal("Storage")
expect(sdn_graph_render_html(draw_label_only)).to_contain(">Storage</button>")
expect(draw_layer_only.nodes[1].layer).to_equal("front")
expect(draw_ordered.accepted).to_be(true)
expect(draw_ordered.graph.nodes[1].id).to_equal("A")
expect(draw_role_only.nodes[1].role).to_equal("database")
expect(draw_duplicate.accepted).to_be(true)
expect(draw_duplicate.graph.nodes[2].id).to_equal("B_copy")
expect(sdn_graph_render_html(draw_duplicate.graph)).to_contain("data-node=\"B_copy\"")
expect(sdn_graph_render_html(draw_canvas)).to_contain("data-canvas-grid=\"24\"")
expect(sdn_graph_render_html(draw_canvas)).to_contain("background-image:radial-gradient(circle,#cbd5e1 1px,transparent 1px)")
expect(sdn_graph_render_html(draw_canvas)).to_contain("background-size:24px 24px")
expect(sdn_graph_render_html_with_selection(draw_role_only, "B", 0)).to_contain("data-selected=\"true\" aria-selected=\"true\"")
expect(inspected_draw_node.found).to_be(true)
expect(inspected_draw_node.parent).to_equal("A")
expect(inspected_draw_node.shape).to_equal("cylinder")
expect(inspected_draw_node.role).to_equal("database")
expect(inspected_draw_node.child_count).to_equal("0")
expect(inspected_draw_node.child_bounds).to_equal("")
expect(inspected_draw_edge.found).to_be(true)
expect(inspected_draw_edge.label).to_equal("approved")
expect(inspected_draw_edge.css).to_equal("warning dashed")
expect(inspected_draw_edge.route).to_equal("orthogonal")
expect(inspected_draw_edge.label_x).to_equal("140")
expect(inspected_draw_edge.label_y).to_equal("32")
expect(inspected_draw_edge.path).to_equal("M 80,10 L 120,10 L 120,40 L 160,40 L 160,10")
expect(draw_aligned.accepted).to_be(true)
expect(draw_aligned.graph.nodes[0].x).to_equal("0")
expect(draw_distributed.accepted).to_be(true)
expect(draw_distributed.graph.nodes[0].x).to_equal("120")
expect(draw_distributed.graph.nodes[2].x).to_equal("60")
expect(catalog[5].owner_module).to_equal("app.office.ui_editor")
expect(catalog[5].features.join(",")).to_contain("selection")
expect(catalog[5].features.join(",")).to_contain("inspector")
expect(catalog[5].features.join(",")).to_contain("style-tokens")
expect(catalog[5].features.join(",")).to_contain("auto-layout")
expect(catalog[5].features.join(",")).to_contain("constraints")
expect(catalog[5].features.join(",")).to_contain("layout-edit")
expect(catalog[5].features.join(",")).to_contain("node-duplicate")
expect(catalog[5].features.join(",")).to_contain("align-layout")
expect(catalog[5].features.join(",")).to_contain("distribute-layout")
expect(catalog[5].features.join(",")).to_contain("layer-edit")
expect(catalog[5].features.join(",")).to_contain("style-token-edit")
expect(catalog[5].actions.join(",")).to_contain("export-ui-sdd")
expect(catalog[5].actions.join(",")).to_contain("ui-layout-edit")
expect(catalog[5].actions.join(",")).to_contain("ui-duplicate-node")
expect(catalog[5].actions.join(",")).to_contain("ui-auto-layout-edit")
expect(catalog[5].actions.join(",")).to_contain("ui-constraints-edit")
expect(catalog[5].actions.join(",")).to_contain("ui-align-selection")
expect(catalog[5].actions.join(",")).to_contain("ui-distribute-selection")
expect(catalog[5].actions.join(",")).to_contain("ui-layer-edit")
expect(catalog[5].actions.join(",")).to_contain("ui-style-token-read")
expect(catalog[5].actions.join(",")).to_contain("ui-style-token-edit")
expect(catalog[5].actions.join(",")).to_contain("ui-inspect-node")
val ui_design = office_ui_design_parse("design: Feature Check\nnode button|Run|button|16|16|80|32|primary|controls|action\nnode label|Label|text|140|24|60|20|secondary|controls|copy\nnode icon|Icon|icon|240|36|24|24|ghost|controls|symbol")
val moved_ui = office_ui_design_update_layout_checked(ui_design, "button", "16", "16", "80", "32", "24", "32", "96", "40")
val layered_ui = office_ui_design_update_layer_checked(moved_ui.design, "button", "controls", "3")
val styled_ui = office_ui_design_update_style_token_checked(layered_ui.design, "button", "primary", "accent")
val duplicated_ui = office_ui_design_duplicate_node_checked(styled_ui.design, "button", "button_copy", "120", "0")
val parented_ui = office_ui_design_set_parent_checked(duplicated_ui.design, "label", "", "button")
val auto_layout_ui = office_ui_design_update_auto_layout_checked(parented_ui.design, "button", "off", "0", "0,0,0,0", "vertical", "4", "4,4,4,4")
val constrained_ui = office_ui_design_update_constraint_checked(auto_layout_ui.design, "label", "left", "top", "stretch", "top")
val resolved_auto_ui = office_ui_design_resolve_auto_layout(constrained_ui.design)
val align_ids = ["button", "label", "icon"]
val align_signature = office_ui_design_geometry_signature(resolved_auto_ui, align_ids)
val aligned_ui = office_ui_design_align_checked(resolved_auto_ui, align_ids, align_signature, "middle")
val distribute_signature = office_ui_design_geometry_signature(aligned_ui.design, align_ids)
val distributed_ui = office_ui_design_distribute_checked(aligned_ui.design, align_ids, distribute_signature, "horizontal")
expect(moved_ui.reason).to_equal("updated")
expect(office_ui_design_render_html(ui_design)).to_contain("data-format=\"html-ui\"")
expect(office_ui_design_render_html(ui_design)).to_contain("data-canvas-width=\"960\"")
expect(office_ui_design_render_html(ui_design)).to_contain("data-frame-count=\"0\"")
expect(office_ui_design_render_html(ui_design)).to_contain("data-component-count=\"3\"")
expect(layered_ui.reason).to_equal("updated")
expect(styled_ui.reason).to_equal("updated")
expect(duplicated_ui.reason).to_equal("updated")
expect(duplicated_ui.design.nodes[3].id).to_equal("button_copy")
expect(parented_ui.reason).to_equal("updated")
expect(auto_layout_ui.reason).to_equal("updated")
expect(constrained_ui.reason).to_equal("updated")
expect(aligned_ui.reason).to_equal("updated")
expect(distributed_ui.reason).to_equal("updated")
expect(office_ui_design_render_html(distributed_ui.design)).to_contain("data-z-index=\"3\"")
expect(office_ui_design_render_html(distributed_ui.design)).to_contain("office-ui-css-accent")
expect(office_ui_design_render_html(distributed_ui.design)).to_contain("data-layout-mode=\"vertical\"")
expect(office_ui_design_render_html(distributed_ui.design)).to_contain("data-constraint-h=\"stretch\"")
expect(office_ui_design_render_html_with_selection(distributed_ui.design, "button")).to_contain("data-selected=\"true\"")
val inspected_ui = office_ui_design_inspect_node(distributed_ui.design, "button")
expect(inspected_ui.found).to_be(true)
expect(inspected_ui.reason).to_equal("selected")
expect(inspected_ui.css).to_equal("accent")
expect(inspected_ui.z_index).to_equal("3")
expect(office_ui_design_read_style_token(distributed_ui.design, "button").css).to_equal("accent")
expect(office_ui_design_to_sdd(distributed_ui.design)).to_contain("button, Run, accent, action, rounded, 24, 28, 96, 40, 3, , vertical, 4")
expect(office_ui_design_to_sdd(distributed_ui.design)).to_contain("label, Label, secondary, copy, rounded")
expect(office_ui_design_to_sdd(duplicated_ui.design)).to_contain("button_copy, Run, accent, action, rounded, 144, 32, 96, 40, 3")
expect(catalog[6].owner_module).to_equal("app.office.base_db")
expect(catalog[6].features.join(",")).to_contain("schema-validation")
expect(catalog[6].features.join(",")).to_contain("html-render")
expect(catalog[6].features.join(",")).to_contain("count-where")
expect(catalog[6].features.join(",")).to_contain("update-where")
expect(catalog[6].features.join(",")).to_contain("delete-where")
expect(catalog[6].actions.join(",")).to_contain("query-table")
expect(catalog[6].actions.join(",")).to_contain("render-base-table-html")
expect(catalog[6].actions.join(",")).to_contain("db-edit")
val base_query_count_action = office_action_dispatch("query-table", "count-where|status|open\ntable: Feature\ncolumns: id,status\nrow: 1,open\nrow: 2,done")
val base_query_select_action = office_action_dispatch("query-table", "select-where|status|open\ntable: Feature\ncolumns: id,status\nrow: 1,open\nrow: 2,done")
val base_query_project_action = office_action_dispatch("query-table", "project-column|status\ntable: Feature\ncolumns: id,status\nrow: 1,open\nrow: 2,done")
val base_missing_query_column_action = office_action_dispatch("query-table", "count-where|missing|open\ntable: Feature\ncolumns: id,status\nrow: 1,open")
val base_html_action = office_action_dispatch("render-base-table-html", "table: Feature\ncolumns: id,status\nrow: 1,<open>\nrow: 2,done")
val base_duplicate_column_action = office_action_dispatch("render-base-table-html", "table: Feature\ncolumns: id,status,status\nrow: 1,open,open")
val base_blank_column_action = office_action_dispatch("render-base-table-html", "table: Feature\ncolumns: id,,status\nrow: 1,open,open")
val base_blank_name_action = office_action_dispatch("render-base-table-html", "table: \ncolumns: id,status\nrow: 1,open")
val base_insert_action = office_action_dispatch("db-edit", "insert|3,open\ntable: Feature\ncolumns: id,status\nrow: 1,done")
val base_update_action = office_action_dispatch("db-edit", "update-where|status|open|status|done\ntable: Feature\ncolumns: id,status\nrow: 1,open\nrow: 2,done")
val base_delete_action = office_action_dispatch("db-edit", "delete-where|status|open\ntable: Feature\ncolumns: id,status\nrow: 1,open\nrow: 2,done")
val base_bad_insert_action = office_action_dispatch("db-edit", "insert|3\ntable: Feature\ncolumns: id,status\nrow: 1,done")
val base_empty_cell_action = office_action_dispatch("db-edit", "insert|3,\ntable: Feature\ncolumns: id,status\nrow: 1,done")
expect(base_query_count_action.output).to_equal("1")
expect(base_query_select_action.output).to_contain("row: 1,open")
expect(base_query_project_action.output).to_contain("open")
expect(base_missing_query_column_action.reason).to_equal("missing-column")
expect(base_html_action.output).to_contain("data-format=\"base-table\"")
expect(base_html_action.output).to_contain("data-column-count=\"2\"")
expect(base_html_action.output).to_contain("data-row-count=\"2\"")
expect(base_html_action.output).to_contain("&lt;open&gt;")
expect(base_duplicate_column_action.reason).to_equal("duplicate-column")
expect(base_blank_column_action.reason).to_equal("blank-column")
expect(base_blank_name_action.reason).to_equal("missing-table-name")
expect(base_insert_action.output).to_contain("row: 3,open")
expect(base_update_action.output).to_contain("row: 1,done")
expect(base_delete_action.output).to_contain("row: 2,done")
expect(base_bad_insert_action.reason).to_equal("row-width-mismatch")
expect(base_empty_cell_action.output).to_contain("row: 3,")
var base_table = new_table("Feature", ["id", "status"])
val inserted_base = insert_row_checked(base_table, ["1", "open"])
base_table = inserted_base.table
base_table = insert_row_checked(base_table, ["2", "open"]).table
val updated_base = update_where(base_table, "status", "open", "status", "done")
val deleted_base = delete_where(updated_base.table, "status", "done")
expect(inserted_base.accepted).to_be(true)
expect(updated_base.affected_count).to_equal(2)
expect(count_where(updated_base.table, "status", "done")).to_equal(2)
expect(deleted_base.accepted).to_be(true)
expect(row_count(deleted_base.table)).to_equal(0)
expect(catalog[7].features.join(",")).to_contain("mathml")
expect(catalog[7].features.join(",")).to_contain("fraction")
expect(catalog[7].features.join(",")).to_contain("subscript")
expect(catalog[7].features.join(",")).to_contain("fenced-group")
expect(catalog[7].features.join(",")).to_contain("precedence-parser")
expect(catalog[7].features.join(",")).to_contain("checked-rendering")
expect(catalog[7].actions.join(",")).to_contain("render-mathml")
expect(catalog[7].actions.join(",")).to_contain("render-math-structure")
expect(catalog[7].actions.join(",")).to_contain("render-mathml-checked")
val mathml_action = office_action_dispatch("render-mathml", "frac(1, 2)")
val math_checked_action = office_action_dispatch("render-mathml-checked", "a + b * c")
val math_bad_action = office_action_dispatch("render-mathml-checked", "a +")
val math_structure_action = office_action_dispatch("render-math-structure", "sqrt(x^2)")
expect(mathml_action.output).to_contain("data-format=\"mathml\"")
expect(mathml_action.output).to_contain("data-token-count=\"6\"")
expect(mathml_action.output).to_contain("<mfrac><mn>1</mn><mn>2</mn></mfrac>")
expect(math_checked_action.output).to_contain("<mi>a</mi><mo>+</mo>")
expect(math_bad_action.reason).to_equal("syntax-error")
expect(math_bad_action.output).to_contain("<math")
expect(math_structure_action.output).to_contain("contains=square-root")
expect(math_structure_action.output).to_contain("contains=superscript")
expect(math_to_mathml("frac(1, 2)")).to_contain("<mfrac><mn>1</mn><mn>2</mn></mfrac>")
expect(math_to_mathml("a + b * c")).to_contain("<mi>a</mi><mo>+</mo><mrow><mi>b</mi><mo>*</mo><mi>c</mi></mrow>")
expect(math_to_mathml_checked("a +").reason).to_equal("syntax-error")
expect(math_fraction("x + 1", "y")).to_contain("<mrow><mi>x</mi><mo>+</mo><mn>1</mn></mrow>")
expect(math_subscript("x", "i")).to_contain("<msub><mi>x</mi><mi>i</mi></msub>")
expect(math_fenced("(", "x + y", ")")).to_contain("<mo>(</mo><mi>x</mi><mo>+</mo><mi>y</mi><mo>)</mo>")
expect(catalog[8].actions.join(",")).to_contain("counter-action")
val counter_inc_action = office_action_dispatch("counter-action", "41|counter_increment")
val counter_dec_action = office_action_dispatch("counter-action", "41|counter_decrement")
val counter_reset_action = office_action_dispatch("counter-action", "5|counter_reset")
val counter_bad_action = office_action_dispatch("counter-action", "5|counter_spin")
val counter_overflow_action = office_action_dispatch("counter-action", "9223372036854775808|counter_increment")
expect(counter_inc_action.output).to_contain("value=42")
expect(counter_inc_action.reason).to_equal("incremented")
expect(counter_dec_action.output).to_contain("value=40")
expect(counter_reset_action.output).to_contain("value=0")
expect(counter_bad_action.reason).to_equal("unsupported")
expect(counter_bad_action.output).to_contain("changed=false")
expect(counter_overflow_action.reason).to_equal("invalid-args")
```

</details>

#### checks slide rendering outline and page design through existing office modules

- assert true
- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_slide_compat_probe()
val summary = ide_slide_compat_summary()
expect(probe.owner_module).to_equal("app.office.slides")
expect(probe.slide_count).to_equal(2)
expect(probe.thumbnail).to_contain("Slide 2:")
expect(probe.canvas_widget_count).to_be_greater_than(1)
expect(probe.outline_line_count).to_equal(2)
expect(probe.design_count).to_equal(2)
assert_true(probe.has_css_like_design)
assert_true(probe.has_outline_transform)
assert_true(probe.has_ppt_html_render)
assert_true(probe.has_safe_css_color)
assert_true(probe.has_positioned_elements)
assert_true(probe.has_element_metadata)
expect(summary).to_contain("transform=true")
expect(summary).to_contain("ppt_html=true")
expect(summary).to_contain("safe_css=true")
expect(summary).to_contain("positioned=true")
expect(summary).to_contain("element_meta=true")
```

</details>

#### checks slide constructor helpers used by IDE presentation previews

- kind: SlideElementKind TextBox
- kind: SlideElementKind TextBox
   - Expected: slide_layout_display_name(base.layout) equals `Title + Content`
   - Expected: slide_layout_short_name(base.layout) equals `Content`
   - Expected: base.elements.len() equals `1`
   - Expected: next.elements.len() equals `2`
   - Expected: next.background equals `#FFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = SlideElement(
    id: "notes",
    kind: SlideElementKind.TextBox(content: "Speaker notes"),
    x: 10,
    y: 20,
    width: 300,
    height: 80
)
val base = slide_with_elements("manual", SlideLayout.TitleContent, [el])
val next = add_slide_element(base, SlideElement(
    id: "footer",
    kind: SlideElementKind.TextBox(content: "Footer"),
    x: 10,
    y: 520,
    width: 300,
    height: 40
))
expect(slide_layout_display_name(base.layout)).to_equal("Title + Content")
expect(slide_layout_short_name(base.layout)).to_equal("Content")
expect(base.elements.len()).to_equal(1)
expect(next.elements.len()).to_equal(2)
expect(next.background).to_equal("#FFFFFF")
```

</details>

#### checks spreadsheet compatibility through existing sheet and formula modules

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compat = ide_sheet_compat_probe()
val summary = ide_sheet_compat_summary()
expect(compat.owner_module).to_equal("app.office.sheets")
expect(compat.compatible_formats.join(",")).to_contain("xlsx")
expect(compat.compatible_formats.join(",")).to_contain("tabular")
expect(compat.sample_range).to_equal("A1:C1")
assert_true(compat.formula_evaluator_ok)
expect(compat.formula_display_recalc).to_be(true)
expect(summary).to_contain("formula=5")
expect(summary).to_contain("evaluator=true")
expect(summary).to_contain("display_recalc=true")
```

</details>

#### checks shared Office numeric parsing used by sheet and planner surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(office_parse_non_negative_i32("4096")).to_equal(4096)
expect(office_parse_non_negative_i32("12px")).to_equal(0)
expect(office_parse_unsigned_decimal_f64("12.5")).to_equal(12.5)
expect(office_parse_signed_decimal_f64("-3.25")).to_equal(-3.25)
expect(office_pow10_f64(2)).to_equal(100.0)
expect(office_pow10_i64(3)).to_equal(1000)
```

</details>

#### checks DB admin targets through existing editor and portal DB ownership

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = ide_db_admin_surface()
val summary = ide_db_admin_summary()
expect(surface.owner_modules.join(",")).to_contain("std.editor.core.session_db")
expect(surface.owner_modules.join(",")).to_contain("app.simple_portal.content_db")
expect(surface.owner_modules.join(",")).to_contain("std.simple_db_if.storage_api")
expect(surface.supported_targets.join(",")).to_contain("simple-db")
expect(surface.simple_db_contracts.join(",")).to_contain("PageBuf")
expect(surface.default_state_mode).to_equal("normal")
expect(summary).to_contain("targets=4")
expect(summary).to_contain("page-size=4096")
```

</details>

#### checks agent dashboard integration through existing editor MCP tools

- assert true
- assert true
   - Expected: surface.lanes.len() equals `3`
   - Expected: surface.gates.len() equals `6`
   - Expected: surface.lanes[0].provider equals `spark`
   - Expected: surface.lanes[0].status equals `unavailable`
   - Expected: surface.lanes[0].source_module equals `assistant.control_plane`
   - Expected: surface.lanes[0].review_gate_id equals `spark-output-reviewed`
   - Expected: surface.lanes[0].degraded_reason equals `spark-unavailable`
   - Expected: surface.lanes[1].provider equals `normal`
   - Expected: surface.lanes[2].role equals `review`
   - Expected: surface.gates[0].gate_id equals `spark-output-reviewed`
   - Expected: surface.gates[0].status equals `blocked`
   - Expected: surface.gates[0].reason equals `spark-unavailable`
   - Expected: surface.gates[3].gate_id equals `mcp-tool-registry-present`
   - Expected: surface.gates[3].status equals `ready`
   - Expected: surface.blocked_count equals `2`
   - Expected: surface.handoff_status equals `degraded-review-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = ide_agent_dashboard_surface()
val summary = ide_agent_dashboard_summary()
expect(surface.owner_module).to_equal("app.editor.mcp_tools")
expect(surface.tool_count).to_be_greater_than(10)
expect(surface.lsp_tool_count).to_equal(10)
expect(surface.wiki_tool_count).to_equal(3)
expect(surface.required_tool_count).to_equal(3)
expect(surface.source_of_truth).to_equal("assistant.control_plane")
assert_true(surface.has_lsp_tools)
assert_true(surface.has_wiki_tools)
expect(surface.modes.join(",")).to_contain("combined-live")
expect(surface.lanes.len()).to_equal(3)
expect(surface.gates.len()).to_equal(6)
expect(surface.lanes[0].provider).to_equal("spark")
expect(surface.lanes[0].status).to_equal("unavailable")
expect(surface.lanes[0].source_module).to_equal("assistant.control_plane")
expect(surface.lanes[0].review_gate_id).to_equal("spark-output-reviewed")
expect(surface.lanes[0].degraded_reason).to_equal("spark-unavailable")
expect(surface.lanes[1].provider).to_equal("normal")
expect(surface.lanes[2].role).to_equal("review")
expect(surface.gates[0].gate_id).to_equal("spark-output-reviewed")
expect(surface.gates[0].status).to_equal("blocked")
expect(surface.gates[0].required).to_be(true)
expect(surface.gates[0].reason).to_equal("spark-unavailable")
expect(surface.gates[3].gate_id).to_equal("mcp-tool-registry-present")
expect(surface.gates[3].status).to_equal("ready")
expect(surface.blocked_count).to_equal(2)
expect(surface.degraded_reasons.join(",")).to_contain("spark-unavailable")
expect(surface.ready_for_integration).to_be(false)
expect(surface.handoff_status).to_equal("degraded-review-required")
expect(summary).to_contain("modes=3")
expect(summary).to_contain("team=3")
expect(summary).to_contain("blocked=2")
```

</details>

#### fails closed when agent dashboard evidence is missing or malformed

- mcp tool
- mcp tool
   - Expected: partial_surface.tool_count equals `2`
   - Expected: partial_surface.required_tool_count equals `3`
   - Expected: partial_surface.gates[3].status equals `missing`
   - Expected: partial_surface.gates[3].reason equals `required-tool-count-missing`
- IdeAgentDashboardLane
- IdeAgentDashboardLane
   - Expected: missing_review_surface.gates[1].status equals `missing`
   - Expected: missing_review_surface.gates[1].reason equals `normal-review-lane-missing`
- IdeAgentDashboardLane
- IdeAgentDashboardLane
   - Expected: missing_spark_surface.gates[0].status equals `missing`
   - Expected: missing_spark_surface.gates[0].reason equals `spark-lane-missing`
- IdeAgentDashboardLane
   - Expected: invalid_surface.gates[2].gate_id equals `lane-status-valid`
   - Expected: invalid_surface.gates[2].status equals `blocked`
   - Expected: invalid_surface.gates[2].reason equals `invalid-lane`
- IdeAgentDashboardLane
- IdeAgentDashboardLane
   - Expected: spoofed_surface.gates[1].status equals `missing`
   - Expected: spoofed_surface.gates[2].status equals `blocked`
   - Expected: spoofed_surface.gates[2].reason equals `invalid-lane`


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_surface = ide_agent_dashboard_surface_from_tools([], ide_agent_dashboard_default_lanes())
expect(empty_surface.tool_count).to_equal(0)
expect(empty_surface.gates[3].status).to_equal("missing")
expect(empty_surface.gates[4].reason).to_equal("lsp-tools-missing")
expect(empty_surface.gates[5].reason).to_equal("wiki-tools-missing")
expect(empty_surface.ready_for_integration).to_be(false)
expect(empty_surface.degraded_reasons.join(",")).to_contain("mcp-tool-registry-empty")

val partial_tools = [
    mcp_tool("editor.lsp_probe", "LSP probe"),
    mcp_tool("editor.wiki_probe", "Wiki probe"),
]
val partial_surface = ide_agent_dashboard_surface_from_tools(partial_tools, ide_agent_dashboard_default_lanes())
expect(partial_surface.tool_count).to_equal(2)
expect(partial_surface.required_tool_count).to_equal(3)
expect(partial_surface.gates[3].status).to_equal("missing")
expect(partial_surface.gates[3].reason).to_equal("required-tool-count-missing")
expect(partial_surface.ready_for_integration).to_be(false)

val missing_review = [
    IdeAgentDashboardLane(lane_id: "spark-research", provider: "spark", role: "fast-explorer", status: "reviewed", requires_review: true, source_module: "assistant.control_plane", review_gate_id: "spark-output-reviewed", degraded_reason: ""),
    IdeAgentDashboardLane(lane_id: "normal-implementation", provider: "normal", role: "implementation", status: "ready", requires_review: false, source_module: "assistant.control_plane", review_gate_id: "normal-review-available", degraded_reason: ""),
]
val missing_review_surface = ide_agent_dashboard_surface_from_tools([], missing_review)
expect(missing_review_surface.gates[1].status).to_equal("missing")
expect(missing_review_surface.gates[1].reason).to_equal("normal-review-lane-missing")
expect(missing_review_surface.ready_for_integration).to_be(false)

val missing_spark = [
    IdeAgentDashboardLane(lane_id: "normal-implementation", provider: "normal", role: "implementation", status: "ready", requires_review: false, source_module: "assistant.control_plane", review_gate_id: "normal-review-available", degraded_reason: ""),
    IdeAgentDashboardLane(lane_id: "normal-review", provider: "normal", role: "review", status: "ready", requires_review: false, source_module: "assistant.control_plane", review_gate_id: "normal-review-available", degraded_reason: ""),
]
val missing_spark_surface = ide_agent_dashboard_surface_from_tools(partial_tools, missing_spark)
expect(missing_spark_surface.gates[0].status).to_equal("missing")
expect(missing_spark_surface.gates[0].reason).to_equal("spark-lane-missing")
expect(missing_spark_surface.ready_for_integration).to_be(false)

val invalid_lane = [
    IdeAgentDashboardLane(lane_id: "mystery", provider: "unknown", role: "review", status: "maybe", requires_review: false, source_module: "assistant.control_plane", review_gate_id: "normal-review-available", degraded_reason: "invalid-test-lane"),
]
val invalid_surface = ide_agent_dashboard_surface_from_tools([], invalid_lane)
expect(invalid_surface.gates[2].gate_id).to_equal("lane-status-valid")
expect(invalid_surface.gates[2].status).to_equal("blocked")
expect(invalid_surface.gates[2].reason).to_equal("invalid-lane")
expect(invalid_surface.ready_for_integration).to_be(false)

val spoofed_review = [
    IdeAgentDashboardLane(lane_id: "spark-research", provider: "spark", role: "fast-explorer", status: "reviewed", requires_review: true, source_module: "assistant.control_plane", review_gate_id: "spark-output-reviewed", degraded_reason: ""),
    IdeAgentDashboardLane(lane_id: "normal-review", provider: "normal", role: "review", status: "ready", requires_review: false, source_module: "dashboard.local", review_gate_id: "normal-review-available", degraded_reason: "spoofed-review"),
]
val spoofed_surface = ide_agent_dashboard_surface_from_tools(partial_tools, spoofed_review)
expect(spoofed_surface.gates[1].status).to_equal("missing")
expect(spoofed_surface.gates[2].status).to_equal("blocked")
expect(spoofed_surface.gates[2].reason).to_equal("invalid-lane")
expect(spoofed_surface.ready_for_integration).to_be(false)
```

</details>

#### checks markdown rendering through the shared editor renderer and preview pane

- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_markdown_render_probe()
val summary = ide_markdown_render_summary()
expect(probe.owner_module).to_equal("std.editor.render.md_renderer")
expect(probe.block_count).to_be_greater_than(2)
expect(probe.rendered_line_count).to_be_greater_than(2)
expect(probe.preview_line_count).to_be_greater_than(2)
assert_true(probe.contains_heading)
assert_true(probe.contains_table)
assert_true(probe.css_document)
assert_true(probe.escapes_html)
assert_true(probe.preview_metadata)
expect(summary).to_contain("preview=")
expect(summary).to_contain("css_doc=true")
expect(summary).to_contain("escaped=true")
expect(summary).to_contain("metadata=true")
```

</details>

#### checks TUI GUI and SDL launch modes through the shared editor launch contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_launch_sanity()
val summary = ide_launch_sanity_summary()
expect(sanity.tui_mode).to_equal("tui")
expect(sanity.gui_mode).to_equal("gui")
expect(sanity.sdl_mode).to_equal("gui-sdl")
expect(sanity.file_count).to_equal(3)
expect(sanity.office_action_count).to_equal(9)
expect(sanity.office_card_count).to_equal(9)
expect(sanity.unknown_option).to_equal("--bad-mode")
expect(summary).to_contain("gui=gui")
expect(summary).to_contain("office_actions=9")
```

</details>

#### checks TUI preview and outline panels through shared editor render helpers

- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_tui_sanity()
val summary = ide_tui_sanity_summary()
expect(sanity.preview_line_count).to_be_greater_than(2)
expect(sanity.outline_line_count).to_equal(2)
assert_true(sanity.renders_markdown_preview)
assert_true(sanity.renders_table_preview)
assert_true(sanity.renders_slide_outline)
assert_true(sanity.renders_outline_style)
expect(summary).to_contain("slide-outline=true")
```

</details>

#### checks GUI rendering through the shared editor backend

- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_gui_sanity()
val summary = ide_gui_sanity_summary()
expect(sanity.theme).to_equal("dark")
assert_true(sanity.renders_markdown)
assert_true(sanity.renders_presentation)
assert_true(sanity.renders_sheet)
assert_true(sanity.has_backend_config)
expect(summary).to_contain("ppt=true")
```

</details>

#### exports IDE app support through the existing plugin manifest registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_plugin_manifest_probe()
val summary = ide_plugin_manifest_summary()
expect(probe.entry_count).to_equal(6)
expect(probe.roundtrip_count).to_equal(6)
expect(probe.libreoffice_entry_count).to_equal(6)
expect(probe.libreoffice_roundtrip_count).to_equal(6)
expect(probe.names.join(",")).to_contain("ide.slides")
expect(probe.names.join(",")).to_contain("ide.draw")
expect(probe.names.join(",")).to_contain("ide.sheets")
expect(probe.manifest_text).to_contain("builtin:app.office.slides")
expect(probe.manifest_text).to_contain("builtin:std.editor.services.sdn_graph")
expect(probe.manifest_text).to_contain("ide_capability_draw")
expect(probe.manifest_text).to_contain("ide_feature_check_draw")
expect(summary).to_contain("roundtrip=6")
expect(summary).to_contain("libre=6")
expect(summary).to_contain("libre_roundtrip=6")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/ide_office_plugin_suite.md](doc/03_plan/sys_test/ide_office_plugin_suite.md)
- **Design:** [doc/05_design/app/office/libreoffice_llm_access.md](doc/05_design/app/office/libreoffice_llm_access.md)
- **Research:** [doc/01_research/app/office/libreoffice_llm_access.md](doc/01_research/app/office/libreoffice_llm_access.md)


</details>
