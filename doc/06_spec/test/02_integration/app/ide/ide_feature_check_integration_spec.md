# ide_feature_check_integration_spec

> IDE feature-check integration specification.

<!-- sdn-diagram:id=ide_feature_check_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_feature_check_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_feature_check_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_feature_check_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ide_feature_check_integration_spec

IDE feature-check integration specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/ide/ide_feature_check_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

IDE feature-check integration specification.
Runs the IDE entrypoint through the Simple CLI so the feature-check manual contract covers real app dispatch.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `feature_check_tui.txt` | TUI capture | `build/test-artifacts/02_integration/app/ide/ide_feature_check_integration/feature_check_tui.txt` |

#### Embedded TUI Text Captures

<details>
<summary>feature_check_tui.txt</summary>

```text
Simple IDE feature check
mode: tui
capabilities: 13
markdown: Markdown Preview [document-renderer] -> std.editor.render.md_renderer (md, markdown)
  check: markdown: std.editor.render.md_renderer blocks=3 lines=6 preview=6 heading=true table=true task_list=true strike=true link=true list=true ordered_list=true quote=true code=true css_doc=true escaped=true metadata=true
  edit-command: md-edit=true stale-reject=true reason=stale-line
writer: Markdown Writer [office-app] -> app.office.word.html_render (writer, md, markdown, html)
  check: writer: app.office.word.html_render markdown=true html=true paper=true escaped=true
slides: Presentation Slides [office-app] -> app.office.slides (ppt, presentation, slides)
  check: slides: app.office.slides count=2 thumb=Slide 2: Roadmap canvas=2 outline=2 designs=2 css=true transform=true ppt_html=true safe_css=true positioned=true element_meta=true
  edit-command: slide-edit=true stale-reject=true reason=stale-slide-element
draw: SDD Diagram Draw [office-app] -> std.editor.services.sdn_graph (draw, diagram, sdd, sdn)
  check: draw: sdn_graph format=sdd name="SDD: Simple Diagram Document" extension=.sdd.sdn nodes=3 edges=2 html=true route=true select=true inspect=true child_meta=true path_meta=true handle_meta=true edit=true geometry=true layer=true order=true role=true node_create=true style_rule=true style_delete=true style_inspect=true edge_create=true edge_duplicate=true edge_label_point=true edge_style=true edge_kind=true reconnect=true delete=true node_delete=true layout=true canvas=true
designer: UI Designer [office-app] -> app.office.ui_editor (figma, html, sdd, ui)
  check: designer: app.office.ui_editor html=true sdd=true selection=true resize_handle_metadata=true
math: Formula Math [office-app] -> app.office.math_editor (math, formula, mathml, equation)
  check: math: app.office.math_editor mathml=true checked=true fraction=true escaped=true
mail: Mail [office-app] -> app.office.mail.mail_app (mail, email, inbox)
  check: mail: app.office.mail.mail_app folders=4 messages=5 unread=2 filtered=2
planner: Planner [office-app] -> app.office.planner.planner_app (planner, tasks, kanban, calendar)
  check: planner: app.office.planner.planner_app tasks=1 view=calendar calendar=2026-1 modified=true
counter: Counter [office-app] -> app.office.counter (counter, state, action)
  check: counter: app.office.counter increment=true decrement=true fail_closed=true
launcher: Office Launcher [office-app] -> app.office.launcher (launcher, home, recent-files)
  check: launcher: app.office.launcher actions=9 cards=9 fail_closed=true
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
  plugin-manifest: plugins: entries=13 roundtrip=13 names=13 kinds=4 libre=6 libre_roundtrip=6
  llm-catalog: apps=11 features=206 actions=128
  llm-apps: Markdown,Writer,Calc,Impress,Draw,Designer,Base,Math,Mail,Planner,Counter
```

</details>

## Scenarios

### IDE feature-check CLI integration

#### prints the complete TUI feature-check manual through the app entrypoint

- Run the IDE feature-check command in TUI mode
   - Expected: code equals `0`
- Review the feature-check header and TUI mode
- Confirm every Office plugin capability is visible
- Capture the TUI report so the manual shows the CLI surface
   - Expected: _write_tui_capture(out) equals `0`
   - Expected: _capture_file_state(out) equals `matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the IDE feature-check command in TUI mode")
val (out, err, code) = _run_ide(["--feature-check", "--tui"])
expect(code).to_equal(0)

step("Review the feature-check header and TUI mode")
expect(out).to_start_with("Simple IDE feature check")
expect(out).to_contain("mode: tui")
expect(out).to_contain("capabilities: 13")

step("Confirm every Office plugin capability is visible")
expect(out).to_contain("markdown: Markdown Preview")
expect(out).to_contain("writer: Markdown Writer")
expect(out).to_contain("writer: app.office.word.html_render markdown=true html=true paper=true escaped=true")
expect(out).to_contain("slides: Presentation Slides")
expect(out).to_contain("draw: SDD Diagram Draw")
expect(out).to_contain("designer: UI Designer")
expect(out).to_contain("designer: app.office.ui_editor html=true sdd=true selection=true resize_handle_metadata=true")
expect(out).to_contain("math: Formula Math")
expect(out).to_contain("math: app.office.math_editor mathml=true checked=true fraction=true escaped=true")
expect(out).to_contain("mail: Mail")
expect(out).to_contain("mail: app.office.mail.mail_app folders=4 messages=5 unread=2 filtered=2")
expect(out).to_contain("planner: Planner")
expect(out).to_contain("planner: app.office.planner.planner_app tasks=1 view=calendar")
expect(out).to_contain("counter: Counter")
expect(out).to_contain("counter: app.office.counter increment=true decrement=true fail_closed=true")
expect(out).to_contain("launcher: Office Launcher")
expect(out).to_contain("launcher: app.office.launcher actions=9 cards=9 fail_closed=true")
expect(out).to_contain("node_create=true")
expect(out).to_contain("style_rule=true")
expect(out).to_contain("style_delete=true")
expect(out).to_contain("style_inspect=true")
expect(out).to_contain("order=true")
expect(out).to_contain("edge_duplicate=true")
expect(out).to_contain("node_delete=true")
expect(out).to_contain("canvas=true")
expect(out).to_contain("sheets: Spreadsheet")
expect(out).to_contain("agent-dashboard: Agent Dashboard")
expect(out).to_contain("db-admin: Database Admin")
expect(out).to_contain("plugin-manifest: plugins: entries=13")
expect(out).to_contain("llm-catalog: apps=11 features=206 actions=128")

step("Capture the TUI report so the manual shows the CLI surface")
expect(_write_tui_capture(out)).to_equal(0)
expect(_capture_file_state(out)).to_equal("matched")
```

</details>

#### prints the complete GUI feature-check manual through the app entrypoint

- Run the IDE feature-check command in GUI mode
   - Expected: code equals `0`
- Review the feature-check header and GUI mode
- Confirm GUI launch and panel summaries are visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the IDE feature-check command in GUI mode")
val (out, err, code) = _run_ide(["--feature-check", "--gui"])
expect(code).to_equal(0)

step("Review the feature-check header and GUI mode")
expect(out).to_start_with("Simple IDE feature check")
expect(out).to_contain("mode: gui")

step("Confirm GUI launch and panel summaries are visible")
expect(out).to_contain("gui-backend: theme=dark")
expect(out).to_contain("tui-panels: preview=")
expect(out).to_contain("launch: launch: tui=tui gui=gui sdl=gui-sdl")
```

</details>

#### keeps normal IDE help and unknown option behavior intact

- Open IDE help through the production entrypoint
   - Expected: help_code equals `0`
- Submit an unknown IDE option
   - Expected: bad_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open IDE help through the production entrypoint")
val (help_out, help_err, help_code) = _run_ide(["--help"])
expect(help_code).to_equal(0)
expect(help_out).to_contain("Usage: simple ide")
expect(help_out).to_contain("--feature-check")

step("Submit an unknown IDE option")
val (bad_out, bad_err, bad_code) = _run_ide(["--bad-mode"])
expect(bad_code).to_equal(1)
expect(bad_out).to_contain("Error: unknown option '--bad-mode'")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
