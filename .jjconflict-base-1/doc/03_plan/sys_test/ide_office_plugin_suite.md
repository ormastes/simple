# IDE Office Plugin Suite System Test Plan

## Scope

Validate the restored IDE product surface and Office plugin wiring for:

- Markdown/Writer preview through `std.editor.render.md_renderer`, including
  Markdown-based generated HTML rendering.
- Impress/PPT slides through `app.office.slides`.
- Calc spreadsheet editing through `app.office.sheets`.
- Draw/SDD, Designer, Base, Math, Mail, Planner, dashboard, and DB admin
  capability ownership through IDE plugin manifests.
- Agent dashboard registry through `app.editor.mcp_tools`
- DB admin ownership through editor/session DB and portal DB modules
- TUI, GUI, SDL, help, and unknown-option launch behavior

## Requirements Covered

| ID | Requirement | Evidence |
|----|-------------|----------|
| REQ-001 | IDE feature-check lists the IDE-visible Office plugin capsules from `doc/07_guide/app/ide_office_plugin_suite.md`. | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| REQ-002 | TUI and GUI feature-check reports stay in parity except selected launch mode. | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| REQ-003 | IDE capability owners resolve to plugin-manifest-backed Markdown/Writer, Impress/PPT, Calc, Draw/SDD, Designer, Base, Math, Mail, Planner, dashboard, and DB admin modules. | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| REQ-004 | The real IDE CLI entrypoint prints complete TUI and GUI feature-check manuals. | `test/02_integration/app/ide/ide_feature_check_integration_spec.spl` |
| REQ-005 | Normal IDE help and unknown-option behavior remain intact. | `test/02_integration/app/ide/ide_feature_check_integration_spec.spl` |
| REQ-006 | Shared Office helpers used by Writer HTML render, slides, sheets, Base, and planner paths remain covered. | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| REQ-007 | The TUI feature-check report stays within a 120-column terminal and publishes text capture evidence. | `build/test-artifacts/03_system/app/ide/feature/ide_office_plugin_suite/feature_check_tui.txt` |
| REQ-008 | Generated SSpec docs read as operator manuals and report `0 stubs`. | `doc/06_spec/03_system/app/ide/feature/ide_office_plugin_suite_spec.md` |

## Execution

```bash
SIMPLE_LIB=src bin/simple-interp test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
SIMPLE_LIB=src bin/simple-interp test/02_integration/app/ide/ide_feature_check_integration_spec.spl
SIMPLE_LIB=src bin/simple-interp src/app/ide/main.spl --feature-check --tui
SIMPLE_LIB=src bin/simple-interp src/app/ide/main.spl --feature-check --gui
simple spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl --output doc/06_spec --no-index
bin/simple spec-coverage --by-category
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Manual Outputs

- `doc/06_spec/03_system/app/ide/feature/ide_office_plugin_suite_spec.md`
- `doc/06_spec/02_integration/app/ide/ide_feature_check_integration_spec.md`

## Coverage Notes

The system spec covers module-level contracts, plugin manifest ownership, pure
probes, bounded TUI layout, generated-manual quality, and TUI capture evidence.
The integration spec covers the CLI dispatch path through
`bin/simple run src/app/ide/main.spl`. Together they guard against the previous
failure mode where the original IDE and Office source tree existed only in
examples while the production `src/app/ide` path was missing.
