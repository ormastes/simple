# ide_office_plugin_suite_spec

> Validates that IDE-facing Markdown/Writer, Impress/PPT, Calc, Draw/SDD, Designer, Base, Math, Mail, Planner, dashboard, and database surfaces reuse existing app modules.

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
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ide_office_plugin_suite_spec

Validates that IDE-facing Markdown/Writer, Impress/PPT, Calc, Draw/SDD, Designer, Base, Math, Mail, Planner, dashboard, and database surfaces reuse existing app modules.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/07_guide/app/ide_office_plugin_suite.md |
| Plan | doc/03_plan/sys_test/ide_office_plugin_suite.md |
| Design | doc/04_architecture/ide_plugin_architecture.md |
| Research | N/A |
| Source | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that IDE-facing Markdown/Writer, Impress/PPT, Calc, Draw/SDD,
Designer, Base, Math, Mail, Planner, dashboard, and database surfaces reuse
existing app modules.

**Requirements:** doc/07_guide/app/ide_office_plugin_suite.md
**Plan:** doc/03_plan/sys_test/ide_office_plugin_suite.md
**Design:** doc/04_architecture/ide_plugin_architecture.md
**Research:** N/A

## Examples

Run the IDE feature check in TUI and GUI modes, then verify the generated
plugin manifest exposes all IDE-visible Office capsules.

## Operator Manual

Use this scenario when changing the IDE product surface, Office plugin
manifests, feature-check output, or the generated manual that release
verification reads.

The operator should confirm these surfaces in order:

1. Capability registry
2. Implementation owner mapping
3. TUI and GUI feature-check text
4. Ordered manual surface
5. TUI capture artifact
6. TUI and GUI parity
7. Existing Office slide modules
8. Existing Office sheet modules
9. Shared Office numeric helpers
10. DB admin ownership
11. Agent dashboard registry
12. Markdown/Writer render path
13. Launch-mode sanity
14. TUI preview and outline panels
15. GUI render sanity
16. Plugin manifest roundtrip

## Capability Table

| Capability | Expected owner | Evidence |
|------------|----------------|----------|
| Markdown/Writer | `std.editor.render.md_renderer` | markdown preview and generated HTML render text |
| Impress/PPT | `app.office.slides` | slide probe, thumbnail, outline, design, and transform |
| Calc | `app.office.sheets` | range, formats, formula evaluator, and shared number helpers |
| Draw/SDD | `std.editor.services.sdn_graph` | plugin manifest ownership |
| Designer | `std.common.markdown_visual_editor` | plugin manifest ownership |
| Base | `std.editor.core.session_db` | DB admin surface and plugin manifest ownership |
| Math | `std.common.math_repr` | plugin manifest ownership |
| Mail | `std.hardware.soc_rtl.mailbox` | plugin manifest ownership |
| Planner | `std.nogc_sync_mut.db.query_planner` | plugin manifest ownership |
| Agent dashboard | `app.editor.mcp_tools` | MCP/LSP/wiki dashboard registry |
| DB admin | `std.editor.core.session_db` | editor/session DB and portal DB ownership |

## Expected Feature-Check Shape

The TUI feature-check capture starts with:

1. `Simple IDE feature check`
2. `mode: tui`
3. `capabilities: 11`
4. Markdown/Writer capability row
5. Markdown render check row
6. Markdown edit-command stale-reject row

Then it lists Impress/PPT, Calc, Draw/SDD, Designer, Base, Math, Mail,
Planner, Agent Dashboard, and DB Admin in that order. The final lines must
include TUI panel evidence, launch-mode evidence, and plugin-manifest evidence.

## Verification Reading Guide

The generated manual is acceptable only when:

- the At a Glance table points to this executable spec;
- the TUI capture embeds the complete feature-check text;
- the scenario names describe product behavior, not test plumbing;
- the executable SSpec blocks stay folded below the manual text;
- the plugin manifest scenario proves `entries=11`, `roundtrip=11`, and
  `names=11`;
- no scenario uses `pass_todo` or a placeholder pass;
- the docgen summary reports `0 stubs`;
- `doc/06_spec` contains no misplaced executable `.spl` specs.

## Failure Triage

If the capability count changes, update the capability registry, feature-check
report, plugin manifest assertions, system-test plan, IDE Office guide, and
generated manual together.

If a plugin owner changes, update the registry first, then adjust the matching
owner assertion and feature-check row. Do not hide the mismatch by weakening the
test.

If a capture file is missing, check the app.io file helpers and capture path
before changing feature-check semantics.

If docgen reports a stub, improve this manual text or the scenario metadata
before claiming verification passed.

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
capabilities: 11
markdown: Markdown/Writer [document-renderer] -> std.editor.render.md_renderer (md, markdown, writer, html)
  check: markdown: std.editor.render.md_renderer blocks=3 lines=6 preview=6 heading=true table=true html=true html_heading=true
  edit-command: md-edit=true stale-reject=true reason=stale-line
slides: Impress/PPT [office-app] -> app.office.slides (ppt, presentation, slides)
  check: slides: app.office.slides count=2 thumb=Slide 2: Roadmap canvas=2 outline=2 designs=2 css=true transform=true
  edit-command: slide-edit=true stale-reject=true reason=stale-slide-element
sheets: Calc Spreadsheet [office-app] -> app.office.sheets (excel, xlsx, tabular, csv)
  check: sheets: app.office.sheets formats=excel,xlsx,csv,tabular range=A1:C1 formula=5 evaluator=true
  edit-command: sheet-edit=true stale-reject=true reason=stale-cell
  gui: gui-backend: theme=dark size=1200x800 md=true ppt=true sheet=true config=true
draw-sdd: Draw/SDD [diagram-app] -> std.editor.services.sdn_graph (draw, sdd, sdn)
  check: manifest-only service-token=draw-sdd
designer: Designer [designer-app] -> std.common.markdown_visual_editor (html, css, ui)
  check: manifest-only service-token=designer
base: Base [database-app] -> std.editor.core.session_db (table, database, import)
  check: manifest-only service-token=base
math: Math [formula-app] -> std.common.math_repr (formula, mathml)
  check: manifest-only service-token=math
mail: Mail [mail-app] -> std.hardware.soc_rtl.mailbox (message, folder, compose)
  check: manifest-only service-token=mail
planner: Planner [planner-app] -> std.nogc_sync_mut.db.query_planner (task, board, calendar)
  check: manifest-only service-token=planner
agent-dashboard: Agent Dashboard [dashboard] -> app.editor.mcp_tools (agent, dashboard, mcp)
  check: agent-dashboard: app.editor.mcp_tools tools=19 lsp=true wiki=true tooling=5 modes=3
db-admin: Database Admin [database] -> std.editor.core.session_db (embedded-db, simple-db, portal-db)
  check: db-admin: owners=5 targets=4 state=normal/1 contracts=Rel/BlkNo/Lsn/TxnId/PhysPtr/PageBuf page-size=4096
  tui: tui-panels: preview=4 outline=2 md=true table=true slide-outline=true styled=true
  launch: launch: tui=tui gui=gui sdl=gui-sdl files=3 unknown=--bad-mode
  plugin-manifest: plugins: entries=11 roundtrip=11 names=11
```

</details>

## Scenarios

### IDE office plugin suite capabilities

#### registers IDE office suite plugin capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ids = ide_capability_ids().join(",")
expect(ids).to_contain("markdown")
expect(ids).to_contain("slides")
expect(ids).to_contain("sheets")
expect(ids).to_contain("draw-sdd")
expect(ids).to_contain("designer")
expect(ids).to_contain("base")
expect(ids).to_contain("math")
expect(ids).to_contain("mail")
expect(ids).to_contain("planner")
expect(ids).to_contain("agent-dashboard")
expect(ids).to_contain("db-admin")
```

</details>

#### points each capability at an existing implementation owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = ide_capabilities()
var owners = ""
for cap in caps:
    owners = owners + cap.owner_module + "\n"
expect(owners).to_contain("std.editor.render.md_renderer")
expect(owners).to_contain("app.office.slides")
expect(owners).to_contain("app.office.sheets")
expect(owners).to_contain("std.editor.services.sdn_graph")
expect(owners).to_contain("std.common.markdown_visual_editor")
expect(owners).to_contain("std.common.math_repr")
expect(owners).to_contain("std.nogc_sync_mut.db.query_planner")
expect(owners).to_contain("app.editor.mcp_tools")
expect(owners).to_contain("std.editor.core.session_db")
```

</details>

#### reports GUI and TUI feature checks through the IDE product surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tui_report = ide_feature_check_report("tui").join("\n")
val gui_report = ide_feature_check_report("gui").join("\n")
expect(tui_report).to_contain("mode: tui")
expect(gui_report).to_contain("mode: gui")
expect(tui_report).to_contain("Impress/PPT")
expect(tui_report).to_contain("Draw/SDD")
expect(tui_report).to_contain("Designer")
expect(gui_report).to_contain("Database Admin")
expect(tui_report).to_contain("tui-panels:")
expect(tui_report).to_contain("slides: app.office.slides")
expect(tui_report).to_contain("edit-command: md-edit=true stale-reject=true")
expect(tui_report).to_contain("edit-command: slide-edit=true stale-reject=true")
expect(tui_report).to_contain("edit-command: sheet-edit=true stale-reject=true")
expect(tui_report).to_contain("agent-dashboard: tools=")
expect(tui_report).to_contain("modes=3")
```

</details>

#### keeps the feature-check manual surface complete and ordered

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ide_feature_check_report("tui")
expect(lines.len()).to_equal(32)
expect(lines[0]).to_equal("Simple IDE feature check")
expect(lines[1]).to_equal("mode: tui")
expect(lines[2]).to_equal("capabilities: 11")
expect(lines[3]).to_start_with("markdown:")
expect(lines[5]).to_start_with("  edit-command:")
expect(lines[6]).to_start_with("slides:")
expect(lines[8]).to_start_with("  edit-command:")
expect(lines[9]).to_start_with("sheets:")
expect(lines[11]).to_start_with("  edit-command:")
expect(lines[13]).to_start_with("draw-sdd:")
expect(lines[15]).to_start_with("designer:")
expect(lines[17]).to_start_with("base:")
expect(lines[19]).to_start_with("math:")
expect(lines[21]).to_start_with("mail:")
expect(lines[23]).to_start_with("planner:")
expect(lines[25]).to_start_with("agent-dashboard:")
expect(lines[27]).to_start_with("db-admin:")
expect(lines[31]).to_start_with("  plugin-manifest:")
```

</details>

#### keeps the TUI feature-check layout within terminal width and captures it

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ide_feature_check_report("tui")
val capture = lines.join("\n")
expect(_max_line_width(lines)).to_be_less_than(121)
expect(capture).to_contain("markdown: Markdown/Writer")
expect(capture).to_contain("slides: Impress/PPT")
expect(capture).to_contain("sheets: Calc Spreadsheet")
expect(capture).to_contain("draw-sdd: Draw/SDD")
expect(capture).to_contain("designer: Designer")
expect(capture).to_contain("base: Base")
expect(capture).to_contain("math: Math")
expect(capture).to_contain("mail: Mail")
expect(capture).to_contain("planner: Planner")
expect(capture).to_contain("db-admin: Database Admin")
expect(capture).to_contain("  tui: tui-panels:")
expect(_write_tui_capture(capture)).to_equal(0)
expect(_capture_file_state(capture)).to_equal("matched")
```

</details>

#### keeps GUI and TUI feature-check probes in parity except launch mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
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
expect(tui_lines[16]).to_equal(gui_lines[16])
expect(tui_lines[18]).to_equal(gui_lines[18])
expect(tui_lines[20]).to_equal(gui_lines[20])
expect(tui_lines[22]).to_equal(gui_lines[22])
expect(tui_lines[24]).to_equal(gui_lines[24])
```

</details>

#### checks slide rendering outline and page design through existing office modules

- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
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
expect(summary).to_contain("transform=true")
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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compat = ide_sheet_compat_probe()
val summary = ide_sheet_compat_summary()
expect(compat.owner_module).to_equal("app.office.sheets")
expect(compat.compatible_formats.join(",")).to_contain("xlsx")
expect(compat.compatible_formats.join(",")).to_contain("tabular")
expect(compat.sample_range).to_equal("A1:C1")
assert_true(compat.formula_evaluator_ok)
expect(summary).to_contain("formula=5")
expect(summary).to_contain("evaluator=true")
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


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = ide_agent_dashboard_surface()
val summary = ide_agent_dashboard_summary()
expect(surface.owner_module).to_equal("app.editor.mcp_tools")
expect(surface.tool_count).to_be_greater_than(10)
assert_true(surface.has_lsp_tools)
assert_true(surface.has_wiki_tools)
expect(surface.modes.join(",")).to_contain("combined-live")
expect(summary).to_contain("modes=3")
expect(summary).to_contain("lsp=true")
expect(summary).to_contain("wiki=true")
```

</details>

#### checks markdown rendering through the shared editor renderer and preview pane

- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
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
assert_true(probe.html_document)
assert_true(probe.html_heading)
expect(summary).to_contain("preview=")
expect(summary).to_contain("html=true")
```

</details>

#### checks TUI GUI and SDL launch modes through the shared editor launch contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sanity = ide_launch_sanity()
val summary = ide_launch_sanity_summary()
expect(sanity.tui_mode).to_equal("tui")
expect(sanity.gui_mode).to_equal("gui")
expect(sanity.sdl_mode).to_equal("gui-sdl")
expect(sanity.file_count).to_equal(3)
expect(sanity.unknown_option).to_equal("--bad-mode")
expect(summary).to_contain("gui=gui")
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_plugin_manifest_probe()
val summary = ide_plugin_manifest_summary()
expect(probe.entry_count).to_equal(11)
expect(probe.roundtrip_count).to_equal(11)
expect(probe.names.join(",")).to_contain("ide.slides")
expect(probe.names.join(",")).to_contain("ide.sheets")
expect(probe.names.join(",")).to_contain("ide.draw-sdd")
expect(probe.names.join(",")).to_contain("ide.designer")
expect(probe.names.join(",")).to_contain("ide.base")
expect(probe.names.join(",")).to_contain("ide.math")
expect(probe.names.join(",")).to_contain("ide.mail")
expect(probe.names.join(",")).to_contain("ide.planner")
expect(probe.manifest_text).to_contain("builtin:app.office.slides")
expect(summary).to_contain("roundtrip=11")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/07_guide/app/ide_office_plugin_suite.md](doc/07_guide/app/ide_office_plugin_suite.md)
- **Plan:** [doc/03_plan/sys_test/ide_office_plugin_suite.md](doc/03_plan/sys_test/ide_office_plugin_suite.md)
- **Design:** [doc/04_architecture/ide_plugin_architecture.md](doc/04_architecture/ide_plugin_architecture.md)


</details>
