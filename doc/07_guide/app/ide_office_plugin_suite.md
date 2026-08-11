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
first-wins conflict policy, lazy activation for disk-discovered extensions
with once-per-activation hooks,
Disposable lifecycles, default-deny permissions with canonical path
containment. Writer, Sheets and
Slides route their toolbar/menu actions through `CommandRegistry` instead of
literal `match action:` arms; Sheets formula functions and Slides
layouts/element kinds are extensible registries; Writer saves through a
`DocumentCodec` and Sheets has a formula-preserving workbook codec. Fourteen
builtin manifests are indexed, and `ide_capabilities_live()` reports each
capability's real state (`declared → indexed → activatable → bound`).

Caveat measured 2026-07-30: of those registries, only `CommandRegistry`,
`LanguageIndex` and the event listeners have consumers outside the kernel. The
kernel's `settings.spl` / `menus.spl` / `keybindings.spl` had zero importers and
were **deleted** — settings and keybindings duplicated the live
`lib/editor/00.common/*` stacks the shells already use, and menus had no
contribution point at all (`ExtensionManifest` has no `contributes_menus`).
The manifest still decodes `keybindings` and `themes` contributions that no host
code binds, and `custom_editors` that the Writer/Sheets/Slides builtins declare
but the host never routes to.
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
- Startup reads manifests and builds indexes; plugin activation stays lazy —
  **aspirational for builtins**, which are eagerly activated at host
  construction (see §Implementation status and
  `doc/08_tracking/bug/builtin_extensions_activate_eagerly_2026-07-30.md`).

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

The primary live Calc command is the standalone Phase-3-built artifact:

```bash
office calc [FILE] --tui
```

`FILE` is optional for a new workbook. `simple office` may remain only as a
cached-artifact compatibility delegate; it is not required for application
launch and must not execute raw Office source.

Semantic access is an explicit loopback service attachment. Start Calc with an
available local port and then use the shared `simple.access/v1` operator
protocol against that service:

```bash
office calc [FILE] --tui --ui-access-port PORT
```

The normal `--tui` command remains the human terminal route. It must render the
same 20×30 model; do not treat an old receipt or a source-level controller as
proof that it is attached to a live UI service.

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
feature. A source-entry run may diagnose IDE capability ownership, but it is
not Office CLI/TUI acceptance evidence and must not regenerate its manual.

If an explicit development interpreter is installed, a raw entry may diagnose
IDE capability ownership only:

```bash
bin/simple-interp src/app/ide/main.spl --feature-check --tui
bin/simple-interp src/app/ide/main.spl --feature-check --gui
```

Do not route these diagnostics through a seed-shaped `bin/simple run`; a seed
without `run` is itself the deployment failure being diagnosed.

Verified 2026-07-30: both exit 0 and report 11 capabilities. Four of the 11
(`draw-sdd`, `designer`, `base`, `math`) still report only
`manifest-only service-token=<id>` — no behavioral check runs for them, so a
wrong `owner_module` on those rows would go undetected. That is exactly how
`mail` shipped pointing at `std.hardware.soc_rtl.mailbox` (a GHDL SoC test
peripheral) and `planner` at `std.nogc_sync_mut.db.query_planner` (a SQL query
planner). Both were corrected to `app.office.mail` / `app.office.planner` and
now run real probes:

```text
mail: app.office.mail emails=5 folders=4 inbox=2 unread=2 read-on-select=true compose=true discard=true
planner: app.office.planner tasks=0->1 add=true views=4/4 reject-unknown=true default-view=kanban
```

Note the duplication that hid this: capability rows are declared in
`src/app/ide/capabilities.spl` **and** hardcoded again as literal strings in
`src/app/ide/feature_report.spl`. An `owner_module` fix must change both.

```bash
bin/simple ide --feature-check --tui   # requires a deployed pure-Simple binary
bin/simple ide --feature-check --gui
bin/simple test test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
OFFICE_BINARY="$PWD/bin/office" SIMPLE_TEST_DRIVER="$PWD/bin/simple" SIMPLE_UI_CLIENT="$PWD/bin/simple" bin/simple test test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

The Office SSpec creates one unique run ID and invokes the deployed gate once.
`OFFICE_BINARY` is the application under test; `SIMPLE_TEST_DRIVER` and
`SIMPLE_UI_CLIENT` are orchestration/protocol tools and are not part of its
closure. Building Office with an existing Phase-3 compiler does not require a
full Simple CLI bootstrap. Its visible workflow and folded error/NFR scenarios
consume only that run. As
long as the generated manual carries its stale-evidence banner, AC-5 remains
open. Regenerate only after the focused split-artifact test passes. The docgen
result must read like an operator manual and report `0 stubs`; the final command
must print `0`.

The production IDE entrypoint also exposes
`simple ide --interaction-check [--tui|--gui] [file]`. It opens an editor
session, performs an in-memory edit, runs Markdown diagnostics, and resolves
the canonical Office Sheets launcher action without modifying the file.
`ide_interaction_evidence_spec.spl` verifies this semantic flow through the
canonical UI-access snapshot/event owners before requesting still or motion
capture. When no image-backed capture host is configured, it publishes the
exact `vision.no_image` blocker instead of claiming GUI evidence.
