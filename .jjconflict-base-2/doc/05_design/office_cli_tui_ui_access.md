<!-- codex-design -->
# Office CLI, Calc TUI, and Semantic UI Access Detail Design

## Selected Contract

This is the F1/N1 implementation design derived from the user-selected command,
protocol, identities, formulas, and evidence root. It intentionally does not
create final requirement documents.

## Proposed Production Components

| Component | Suggested path | Responsibility |
|---|---|---|
| IDE startup-light entry | `src/app/ide/cli_entry.spl` | Parse `ide --feature-check --tui|--gui` before global filtering |
| Office startup-light entry | `src/app/office/cli_entry.spl` | Parse `office calc [FILE] --tui`, compatibility aliases, help/errors |
| Calc controller | `src/app/office/sheets/calc_controller.spl` | Own sheet, active cell, pending edit, revision, UI session, render invalidation |
| Calc semantic builder | `src/app/office/sheets/calc_ui_access.spl` | Build `main` surface and stable cell/control nodes |
| Existing Calc TUI | `src/app/office/interactive.spl` | Render/keyboard adapter over controller state |
| Common access CLI | `src/app/ui/access_cli.spl` | Carry value-bearing action input without shell concatenation |
| Formula dispatcher | `src/app/office/sheets/formula.spl` | Canonical `AVG` alias to `AVERAGE` |
| System check gate | `scripts/check/check-office-cli-tui-ui-access.spl` | Launch deployed processes, collect PTY/protocol/perf evidence |

Paths are proposed ownership boundaries; the implementation owner may place a
module beside an established canonical owner if it preserves these interfaces.

## Controller State

`CalcController` should contain:

- workbook/sheet;
- optional file path;
- active cell reference;
- pending formula/value text;
- edit/focus state;
- semantic snapshot revision;
- bounded recent events;
- cached semantic tree/snapshot by revision;
- cached ANSI frame by revision and viewport;
- terminal lifecycle state owned by the launch adapter.

The controller is the only bridge allowed to mutate both sheet and UI session
state.

## Frozen Public Identities

```text
surface: main
root: main#root
cell: main#cell_<A1-reference>
formula input: main#formula_input
confirm: main#confirm_edit
```

The minimum acceptance nodes are `main#cell_A1`,
`main#formula_input`, and `main#confirm_edit`.

## Action Algorithm

### Select a Cell

1. Validate the observed revision and `select` capability.
2. Parse the reference encoded in the canonical ID.
3. Set the active cell.
4. Load its raw value/formula into the formula input.
5. Rebuild the current semantic snapshot and ANSI frame.
6. Record correlated request/action/result events.

### Enter Text

1. Validate that `main#formula_input` advertises `type_text`/`set_value`.
2. Accept text as a typed argv/request field, never shell source.
3. Update pending text and editing/focus state.
4. Advance revision and rebuild visible state.
5. Do not mutate the sheet until confirmation.

### Confirm

1. Validate `main#confirm_edit`, revision, and pending state.
2. Write pending text through `Sheet.set_value`.
3. Recalculate through `recalculate_formula_cells`.
4. Clear editing state while preserving the raw formula for formula-bar display.
5. Rebuild semantic and ANSI views.
6. Record correlated success or typed formula error.

## Formula Design

- `*` continues through `_eval_term`; no new multiplication helper.
- Function names remain case-insensitive through existing normalization.
- `AVG` canonicalizes to `AVERAGE` at the narrow alias boundary.
- Range, empty-input, nonnumeric, and error behavior is inherited from
  `AVERAGE`.
- The system witness uses A1=6, A2=8, B1=`=A1*A2`, C1=`=AVG(A1:A2)`.

## CLI Design

Preferred forms:

```text
simple office calc --tui
simple office calc FILE --tui
simple ide --feature-check --tui
simple ide --feature-check --gui
```

Compatibility forms continue to work, including the existing
`office edit-sheet FILE --tui` route. Unknown options fail with a stable
nonzero diagnostic.

The semantic action form is:

```text
simple ui act --canonical ID --action ACTION --revision N \
  --request-id ID [--value VALUE] --json
```

`--value` is valid only for advertised value-bearing actions. The common
validator rejects it for other actions.

## Live Service and Persistence

Calc explicitly starts the existing loopback access service when UI access is
enabled by its established debug/test configuration. `simple ui` remains the
only operator CLI. Persisted access-store fallback is read-only and rejects
`act`.

History stores at most 64 events. Every accepted action records:

- `access_request` with request ID and target;
- app action/transition;
- `access_result` with the same request ID and stable result code.

## Evidence Gate Interface

The system spec calls:

```text
scripts/check/check-office-cli-tui-ui-access.spl --scenario <name>
```

through the self-hosted `SIMPLE_BINARY`. Frozen scenario names:

- `cli-help`
- `cli-ide`
- `cli-invalid`
- `ui-discovery`
- `ui-action-history`
- `ui-rejection`
- `formula-multiply`
- `formula-avg`
- `formula-invalid`
- `evidence`
- `performance`
- `isolation`

Each scenario launches or connects to the real deployed commands, fails
nonzero on any missing requirement, and emits compact `key=value` receipts.
The SSpec helper names are:

- `setup_office_cli_tui_ui_access`
- `check_office_gate`

There are no silent placeholder helpers. A missing runtime, gate, command,
surface, artifact, or marker is an immediate test failure.

## Evidence Layout

```text
build/test-artifacts/03_system/app/office/feature/office_cli_tui_ui_access/
  tui/calc-before.ansi
  tui/calc-before.txt
  tui/calc-after.ansi
  tui/calc-after.txt
  protocol/windows.json
  protocol/snapshot-before.json
  protocol/surface-main.json
  protocol/find.json
  protocol/actions.json
  protocol/snapshot-after.json
  protocol/history.json
  artifact/formulas.xlsx
  exec/commands.txt
  log/calc-service.log
  perf/metrics.txt
```

## Error and Cleanup

The gate owns bounded startup/health timeouts and always stops the Calc child.
Terminal cleanup is asserted after normal quit, failed action, and forced
service shutdown. Evidence is written atomically enough that stale files cannot
be mistaken for the current run; the gate records a run ID in protocol,
capture, and performance receipts.

## Performance Measurement

Warm measurements use a fixed fixture and multiple samples within one bounded
gate run. The gate reports p95 using the existing nearest-rank convention:

- launch ready <= 2000 ms;
- windows/snapshot p95 <= 100 ms;
- find p95 <= 25 ms;
- action plus observed state p95 <= 250 ms;
- RSS delta <= 20 MiB.

The production request path performs no subprocess, retry sleep, full workbook
scan, or filesystem reread.

## SGTTI Isolation

Only the test/check lane may import `std.ui_test.sgtti` or construct
`SgttiTestDriver`. Production behavior uses `common.ui.access`, `UISession`,
and the normal access service. The isolation gate scans the complete normal
Office/IDE entry and controller closure for SGTTI/test-only markers and also
proves an ordinary non-debug Office invocation does not create access artifacts.
