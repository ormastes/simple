# Standalone Office Binary — Local Research

## Finding

`src/app/office/mod.spl` is the wrong native-build entry for Calc. Its module
closure includes the full Office suite and `app.office.gui`, which reaches the
browser/GPU render stack. `src/app/office/interactive.spl` also imports that GUI,
so taking a single loader function from it still admits the broad closure.

The self-hosted compiler already supports isolated explicit-entry closure
builds. A separate entry therefore does not need compiler bootstrap at launch;
it needs only a normal release build when the artifact is produced.

## Implemented boundary

- `src/app/office_cli/main.spl`: hosted executable entry.
- `src/app/office/calc_cli.spl`: deterministic Calc command grammar.
- `src/app/office/sheets/sheet_io.spl`: file I/O without GUI imports.
- `src/app/office/sheets/calc_tui.spl`: portable model and fixed frame.
- `src/app/office/sheets/calc_tui_host.spl`: hosted raw-terminal adapter.
- `src/os/apps/office_calc/main.spl`: SimpleOS frame-mode entry.

The host closure built successfully with 78 modules and no Office GUI/GPU
link dependency. The existing SimpleOS runtime archive did not link the same
portable entry because it lacks core array/string/file/argument/math ABI
symbols. This is a target-runtime gap, not an Office bootstrap dependency.

## Runtime evidence (2026-08-11)

- Native host artifact: build PASS, 3.6 MiB.
- `--help`: exit 0.
- `calc --frame-once`: 124 columns by 37 lines; A–T and rows 1–30.
- PTY Calc edit: `A1=6`, `A2=8`, `B1=A1*A2`, `C1=AVG(A1:A2)` rendered
  `6`, `48`, and `7`; quit exit 0.
- SimpleOS link: FAIL CLOSED on the incomplete target runtime ABI.

## Existing-work note

Unrelated changes in `src/app/office/file_formats.spl` were preserved.
