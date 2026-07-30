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

## Implementation status (2026-07-29)

The contract above was aspirational when written. What is now actually
implemented, and what is not:

**Real today** — the extension kernel lives in
`src/lib/editor/extensions/` (not `src/app/ide/`): SDN manifests with typed
decode and line/col diagnostics, `CommandRegistry` with typed handlers and
first-wins conflict policy, lazy activation with once-per-activation hooks,
Disposable lifecycles, default-deny permissions with canonical path
containment, and the settings/menus/keybindings registries. Writer, Sheets and
Slides route their toolbar/menu actions through `CommandRegistry` instead of
literal `match action:` arms; Sheets formula functions and Slides
layouts/element kinds are extensible registries; Writer saves through a
`DocumentCodec` and Sheets has a formula-preserving workbook codec. Fourteen
builtin manifests are indexed, and `ide_capabilities_live()` reports each
capability's real state (`declared → indexed → activatable → bound`).
Authoring guide: `doc/07_guide/app/ide/extension_authoring.md`.

**Not yet** — service tokens exist as a type but scoped DI is not wired
through the Office capsules; AOP hooks are limited to activation observation
(no third-party command/render/save interceptors); out-of-process (worker/WASM)
extension hosting is declared in the contract but unimplemented, so all
extensions run in-process; `src/app/office/plugins.spl` still holds three
transitional static `PluginEntry` records; and Office capsules still import
some sibling modules directly. `src/lib/common/ide/` is not the contract home —
the kernel contracts are in `src/lib/editor/extensions/contract.spl`.

DOCX/XLSX/PPTX compatibility is **not** claimed: the codec trait exists, the
format work does not.

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

The `ide` subcommand exists only in the pure-Simple CLI
(`src/app/cli/_CliMain/main_and_help.spl`). When the deployed `bin/simple` is a
Rust bootstrap seed — check with `bin/simple --version`, which then prints
"this Rust-built Simple binary is a bootstrap seed only" — `bin/simple ide`
fails with `error: file not found: ide`, because the seed has no `ide` handler
and treats the word as a filename. That is a **deployment** gap, not a missing
feature: run the entry point directly until a pure-Simple binary is deployed.

```bash
bin/simple run src/app/ide/main.spl --feature-check --tui   # works on a seed
bin/simple run src/app/ide/main.spl --feature-check --gui
```

Verified 2026-07-30: both exit 0 and report 11 capabilities. Note that 6 of the
11 (`draw-sdd`, `designer`, `base`, `math`, `mail`, `planner`) report only
`manifest-only service-token=<id>` — no behavioral check runs for them, which is
why the wrong `owner_module` values on `mail`
(`std.hardware.soc_rtl.mailbox`) and `planner`
(`std.nogc_sync_mut.db.query_planner`) go undetected.

```bash
bin/simple ide --feature-check --tui   # requires a deployed pure-Simple binary
bin/simple ide --feature-check --gui
bin/simple test test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
bin/simple test test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl
bin/simple spipe-docgen test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

The docgen result must read like an operator manual and report `0 stubs`. The
final command must print `0`.
