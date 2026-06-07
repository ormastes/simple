# IDE Office Plugin Suite System Test Plan

## Scope

Validate the restored IDE product surface and Office plugin wiring for:

- Markdown preview through `std.editor.render.md_renderer`
- Presentation slides through `app.office.slides`
- Tabular/spreadsheet editing through `app.office.sheets`
- Agent dashboard registry through `app.editor.mcp_tools`
- DB admin ownership through editor/session DB and portal DB modules
- TUI, GUI, SDL, help, and unknown-option launch behavior

## Requirements Covered

| ID | Requirement | Evidence |
|----|-------------|----------|
| REQ-001 | IDE feature-check lists all five supported capability groups. | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| REQ-002 | TUI and GUI feature-check reports stay in parity except selected launch mode. | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| REQ-003 | IDE capability owners resolve to existing Markdown, Office, editor MCP, and DB modules. | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| REQ-004 | The real IDE CLI entrypoint prints complete TUI and GUI feature-check manuals. | `test/02_integration/app/ide/ide_feature_check_integration_spec.spl` |
| REQ-005 | Normal IDE help and unknown-option behavior remain intact. | `test/02_integration/app/ide/ide_feature_check_integration_spec.spl` |
| REQ-006 | Shared Office helpers used by slides, sheets, and planner paths remain covered. | `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| REQ-007 | The TUI feature-check report stays within a 120-column terminal and publishes text capture evidence. | `build/test-artifacts/03_system/app/ide/feature/ide_office_plugin_suite/feature_check_tui.txt` |

## Execution

```bash
SIMPLE_LIB=src bin/simple-interp test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
SIMPLE_LIB=src bin/simple-interp test/02_integration/app/ide/ide_feature_check_integration_spec.spl
SIMPLE_LIB=src bin/simple-interp src/app/ide/main.spl --feature-check --tui
SIMPLE_LIB=src bin/simple-interp src/app/ide/main.spl --feature-check --gui
bin/simple spec-coverage --by-category
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Manual Outputs

- `doc/06_spec/test/03_system/app/ide/feature/ide_office_plugin_suite_spec.md`
- `doc/06_spec/test/02_integration/app/ide/ide_feature_check_integration_spec.md`

## Coverage Notes

The system spec covers module-level contracts, pure probes, bounded TUI layout,
and TUI capture evidence. The integration spec covers the CLI dispatch path
through `bin/simple run src/app/ide/main.spl`. Together they guard against the
previous failure mode where the original IDE and Office source tree existed only
in examples while the production `src/app/ide` path was missing.
