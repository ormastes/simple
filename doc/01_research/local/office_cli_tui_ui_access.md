# Office CLI, Calc TUI, and Semantic UI Access — Local Research

## Scope

This research covers deployed CLI entry points for Simple IDE and Office,
the live Calc TUI, semantic UI access for debugging/LLM operators, modern
SSpec evidence, multiplication, and the `AVG()` compatibility spelling.

## Current CLI State

- `src/app/cli/_CliMain/main_and_help.spl` delegates `ui`, `play`, and `t32`
  before global option filtering.
- The same global filtering treats `--tui` as a logging/UI option and removes
  it before the later Office branch runs.
- A later `office` branch invokes `src/app/office/mod.spl` through
  `cli_run_file`; this is both too late for `--tui` and an undesirable
  production source-entry path.
- There is no deployed `ide` branch. `bin/simple ide --feature-check --tui`
  is therefore interpreted as a source filename and fails.
- `src/app/ide/main.spl` already implements feature-check behavior, and
  `src/lib/editor/core/launch.spl` already recognizes TUI and GUI modes.

The established precedent is to give commands that own mode-specific options a
startup-light entry function and dispatch them before global filtering.

## Current Calc TUI State

`src/app/office/mod.spl` exposes the live sheet editor as:

```text
simple office edit-sheet FILE --tui
```

That route calls `run_sheet_tui_mode` in
`src/app/office/interactive.spl`. The TUI is real rather than a print-only
mock:

- raw terminal bytes are decoded by `decode_key_byte`;
- `tui_apply_key` owns cursor movement and input buffering;
- Enter writes through `Sheet.set_value`;
- Enter calls `recalculate_formula_cells`;
- `tui_frame` produces the real ANSI screen;
- the loop restores terminal mode when it exits.

The command grammar is not discoverable as Calc, requires a file, and cannot
currently be driven through the canonical semantic UI access surface.

## Formula Findings

Multiplication is already implemented:

- the tokenizer recognizes `*`;
- the term parser applies multiplication before addition;
- the live Calc path recalculates formulas using the real evaluator.

Existing tests already exercise `=A1*2` through the pure TUI state machine.
A live research probe calculated `=A1*A2` with `A1=6`, `A2=8` as `48`.

`AVERAGE(...)` is implemented by `_dispatch_function`, but `AVG(...)` is not a
recognized alias. A live probe produced:

```text
=AVERAGE(A1:A2) -> 7
=AVG(A1:A2)     -> #ERR: Unknown function: AVG
```

The narrow compatible fix is a pure canonical alias:

```text
AVG -> AVERAGE
```

It should be tested through `recalculate_formula_cells` and through the live
Calc UI, not only by calling a math helper.

## Semantic UI Access Findings

The canonical operator protocol already exists under `simple ui`:

```text
windows -> snapshot -> surface -> find -> act -> history
```

It provides the `simple.access/v1` envelope, canonical IDs, revision checks,
bounded history, and live-service or persisted-store transports. Reusing it
keeps Office consistent with other Simple GUI/TUI tools.

Calc is not connected to it today:

- `SheetsApp.build_ui` exposes an opaque table and a non-editable formula text
  node rather than stable per-cell nodes and an editable formula input;
- `SheetsApp` understands app-local edit events, but its callback is not wired
  into generic `UISession` dispatch;
- the current access CLI action grammar does not carry a text value, so it
  cannot express formula entry;
- the raw `TuiState` screen has no semantic adapter or access-store attachment.

The most reusable integration is a Calc controller that owns `SheetsApp` and a
`UISession`, rebuilds the semantic tree after app actions, persists access
events through the existing store, and renders the same sheet state through the
real TUI. Formula input needs a value-bearing action such as `type_text`.
Stable cell nodes should use canonical IDs such as `main#cell_A1`.

The intended live flow is:

1. Launch `simple office calc [FILE] --tui`.
2. Discover the Calc surface through `simple ui windows`.
3. Inspect it with `snapshot`, `surface`, and `find`.
4. Enter `6`, `8`, `=A1*A2`, and `=AVG(A1:A2)` through semantic actions.
5. Observe `48` and `7` in an independent post-action snapshot.
6. Confirm correlated requests/results in bounded history.
7. Capture the real ANSI/text TUI as supplementary visual evidence.

## Modern SSpec Findings

The authoritative precedent is
`test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl`.
A new Office spec should use:

- `use std.spec.*`;
- imperative `step("...")` calls;
- `# @req` traceability;
- `# @manual: show` for the primary operator flow and `folded` for gates;
- typed `# @capture(tui)`, `# @capture(protocol)`, and
  `# @capture(artifact)` evidence;
- fail-fast helpers rather than placeholder passes;
- `# @evidence-display: embed_tui`;
- troubleshooting metadata for launch, access-service, and formula failures.

The system test must execute the deployed CLI, operate the live semantic
surface, assert independent post-state and history, and capture the screen.
A screenshot or direct module import alone does not prove this feature.

Proposed locations:

- executable spec:
  `test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl`
- generated manual:
  `doc/06_spec/03_system/app/office/feature/office_cli_tui_ui_access_spec.md`
- test plan:
  `doc/03_plan/sys_test/office_cli_tui_ui_access.md`
- evidence:
  `build/test-artifacts/03_system/app/office/feature/office_cli_tui_ui_access/`

## Architecture Constraints

- Keep SGTTI and test-only imports out of the production Calc entry path.
- Reuse the canonical UI access grammar and access store.
- Do not introduce a second Office-only automation protocol.
- Avoid raw source execution or a Rust-seed fallback in the deployed command.
- Keep startup and request hot paths free of repeated full-tree scans,
  subprocess calls, and retry sleeps.
- Preserve `edit-sheet FILE --tui`, `sheets`, and existing IDE invocation
  compatibility while adding the ergonomic route.

## Conclusion

The evaluator needs only an `AVG` alias; multiplication is already sound.
The material work is deployed early CLI dispatch plus a Calc controller that
connects the real sheet model/TUI to the existing semantic UI-access protocol.
