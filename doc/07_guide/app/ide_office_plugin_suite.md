# IDE Office Plugin Suite Guide

## Contract

The IDE Office suite is plugin-based. Built-in Office tools register
declarative contributions through the IDE plugin kernel instead of importing
each other's private modules.

Required capsules:

- Markdown/Writer: Markdown document editing, Writer-style blocks/tables, and
  generated HTML render output for preview.
- Impress/PPT: Markdown-backed decks, slide pages, layouts, and presentation
  commands.
- Calc: grids, formulas, charts, and import/export commands.
- Draw/SDD: SDN graph, shape, connector, layout, and export commands.
- Designer: HTML/UI surface, CSS, component tree, assets, and layout commands.
- Base: table/database readback, import, and DB admin commands.
- Math, Mail, Planner, dashboard, and DB admin: feature-check visible capsules
  with declared commands and services.

## Plugin Rules

- Shared contracts live in `src/lib/common/ide/`.
- IDE host/plugin kernel code lives under `src/app/ide/`.
- Office capsules live under `src/app/office/`.
- Sibling Office capsules communicate through contribution points and service
  tokens only.
- Dependency injection uses scoped service tokens: `global`, `workspace`,
  `document`, `surface`, and `request`.
- AOP is limited to declared hooks such as command, document-save, render,
  diagnostics, plugin lifecycle, and invalidation hooks.
- Startup reads manifests and builds indexes; plugin activation stays lazy.

## Feature Check

`--feature-check` must show IDE-visible Office capabilities consistently for
TUI and GUI modes. A capability added to an Office capsule must update:

- `src/app/ide/feature_report.spl`
- `src/app/ide/plugin_manifest.spl`
- `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`
- `doc/06_spec/03_system/app/ide/feature/ide_office_plugin_suite_spec.md`

The deployed operator commands are:

```bash
simple ide --feature-check --tui
simple ide --feature-check --gui
```

Command-specific mode flags are owned by the IDE/Office entry points and must
be delegated before global CLI option filtering. Production commands use
startup-light compiled/in-process owners; raw source execution and Rust-seed
fallback are not accepted deployment paths.

## Calc TUI and LLM Debug Access

The preferred live Calc command is:

```bash
simple office calc [FILE] --tui
```

`FILE` is optional for a new workbook. Existing `sheets` and
`edit-sheet FILE --tui` commands remain compatibility aliases.

Calc exposes its real sheet model through the shared `simple.access/v1`
operator protocol:

```text
simple ui windows
simple ui snapshot
simple ui surface main
simple ui find ...
simple ui act ... --value ...
simple ui history --surface main
```

The semantic tree uses stable cell IDs such as `main#cell_A1`, plus
`main#formula_input` and `main#confirm_edit`. Screen coordinates and a TUI
capture are supporting evidence; independent semantic post-state and correlated
history are the behavioral oracle.

Formula compatibility includes ordinary multiplication and the pure
`AVG(...)` alias of `AVERAGE(...)`. The canonical manual example enters
`A1=6`, `A2=8`, `B1=A1*A2` (result `48`), and
`C1=AVG(A1:A2)` (result `7`).

## Verification

```bash
bin/simple ide --feature-check --tui
bin/simple ide --feature-check --gui
bin/simple test test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
bin/simple test test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl
bin/simple spipe-docgen test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

The docgen result must read like an operator manual and report `0 stubs`. The
final command must print `0`.
