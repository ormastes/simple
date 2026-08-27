# ide_feature_check_integration_spec

> IDE feature-check integration specification.

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
| Updated | 2026-08-26 |
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
capabilities: 11
markdown: Markdown/Writer [document-renderer] -> std.editor.render.md_renderer (md, markdown, writer, html)
  check: markdown: std.editor.render.md_renderer blocks=8 lines=2 prev=0 head=true table=true html=true html_head=true
  edit-command: md-edit=true stale-reject=true reason=stale-line
slides: Impress/PPT [office-app] -> app.office.slides (ppt, presentation, slides)
  check: slides: app.office.slides count=2 thumb=Slide 2: Roadmap canvas=2 outline=2 designs=2 css=true transform=true
  edit-command: slide-edit=true stale-reject=true reason=stale-slide-element
sheets: Calc Spreadsheet [office-app] -> app.office.sheets (excel, xlsx, tabular, csv)
  check: sheets: app.office.sheets formats=excel,xlsx,csv,tabular range=A1:C1 formula=5 evaluator=true
  edit-command: sheet-edit=true stale-reject=true reason=stale-cell
  gui: gui-backend: theme=dark size=1200x800 md=true ppt=true sheet=true config=true
draw-sdd: Draw/SDD [diagram-app] -> std.editor.services.sdn_graph (draw, sdd, sdn)
  check: draw-sdd: std.editor.services.sdn_graph nodes=3 edges=2 async=1 weave=true canonical=3/2 html-nodes=3
designer: Designer [designer-app] -> std.common.markdown_visual_editor (html, css, ui)
  check: designer: std.common.markdown_visual_editor blocks=4 head=1 bull=2 links=2 prev=4:true titles=2/2 md-path=true
base: Base [database-app] -> std.editor.core.session_db (table, database, import)
  check: base: std.editor.core.session_db wal=3 tabs=2 folds=true ckpt=true durable=3 drained=true mode=normal
math: Math [formula-app] -> std.common.math_repr (formula, mathml)
  check: math: std.common.math_repr latex=\frac{a}{b} pretty=(a)/(b) ast=Frac(Id(a), Id(b)) md=true checks=4/4
mail: Mail [mail-app] -> app.office.mail (message, folder, compose)
  check: mail: app.office.mail emails=5 folders=4 inbox=2 unread=2 read-on-select=true compose=true discard=true
planner: Planner [planner-app] -> app.office.planner (task, board, calendar)
  check: planner: app.office.planner tasks=0->1 add=true views=4/4 reject-unknown=true default-view=kanban
agent-dashboard: Agent Dashboard [dashboard] -> app.editor.mcp_tools (agent, dashboard, mcp)
  check: agent-dashboard: app.editor.mcp_tools tools=19 lsp=true wiki=true modes=3
db-admin: Database Admin [database] -> std.editor.core.session_db (embedded-db, simple-db, portal-db)
  check: db-admin: owners=5 targets=4 state=normal/1 contracts=Rel/BlkNo/Lsn/TxnId/PhysPtr/PageBuf page-size=4096
  tui: tui-panels: preview=6 outline=1 md=true table=true slide-outline=true styled=true
  launch: launch: tui=tui gui=gui sdl=gui-sdl files=3 unknown=--bad-mode
  plugin-manifest: plugins: entries=11 roundtrip=11 names=11
saml: SAML Analysis [language-analysis] -> std.common.saml (saml, llm-fn, prompt, schema)
  check: saml: std.common.saml functions=2 diagnostics=4 strong=red_proven weak=unevidenced checks=5/5
```

</details>

## Scenarios

### IDE feature-check CLI integration

#### prints the complete TUI feature-check manual through the app entrypoint

- prints the complete TUI feature-check manual through the app entrypoint
- Run the IDE feature-check command in TUI mode
   - Expected: code equals `0`
- Review the feature-check header and TUI mode
- Confirm every Office plugin capability is visible
- Capture the TUI report so the manual shows the CLI surface
   - Expected: _write_tui_capture(out) equals `0`
   - Expected: _capture_file_state(out) equals `matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prints the complete TUI feature-check manual through the app entrypoint")
step("Run the IDE feature-check command in TUI mode")
val (out, err, code) = _run_ide(["--feature-check", "--tui"])
expect(code).to_equal(0)

step("Review the feature-check header and TUI mode")
expect(out).to_start_with("Simple IDE feature check")
expect(out).to_contain("mode: tui")
expect(out).to_contain("capabilities: 11")

step("Confirm every Office plugin capability is visible")
expect(out).to_contain("markdown: Markdown/Writer")
expect(out).to_contain("slides: Impress/PPT")
expect(out).to_contain("sheets: Calc Spreadsheet")
expect(out).to_contain("mail: Mail")
expect(out).to_contain("planner: Planner")
expect(out).to_contain("agent-dashboard: Agent Dashboard")
expect(out).to_contain("db-admin: Database Admin")
expect(out).to_contain("plugin-manifest: plugins: entries=11")

step("Capture the TUI report so the manual shows the CLI surface")
expect(_write_tui_capture(out)).to_equal(0)
expect(_capture_file_state(out)).to_equal("matched")
```

</details>

#### prints the complete GUI feature-check manual through the app entrypoint

- prints the complete GUI feature-check manual through the app entrypoint
- Run the IDE feature-check command in GUI mode
   - Expected: code equals `0`
- Review the feature-check header and GUI mode
- Confirm GUI launch and panel summaries are visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prints the complete GUI feature-check manual through the app entrypoint")
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

- keeps normal IDE help and unknown option behavior intact
- Open IDE help through the production entrypoint
   - Expected: help_code equals `0`
- Submit an unknown IDE option
   - Expected: bad_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps normal IDE help and unknown option behavior intact")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b9aa835c374aa3244e4ea14815f64a9cf726991a5fb4bb720925cbb48fd5b46`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b9aa835c374aa3244e4ea14815f64a9cf726991a5fb4bb720925cbb48fd5b46`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b9aa835c374aa3244e4ea14815f64a9cf726991a5fb4bb720925cbb48fd5b46`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/app/ide/ide_feature_check_integration_spec.spl
mirror: doc/06_spec/02_integration/app/ide/ide_feature_check_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/ide/ide_feature_check_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/ide/ide_feature_check_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/ide/ide_feature_check_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/ide/ide_feature_check_integration_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints the complete GUI feature-check manual through the app entrypoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/ide/ide_feature_check_integration_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps normal IDE help and unknown option behavior intact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
