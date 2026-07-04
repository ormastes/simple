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

## Verification

```bash
bin/simple-interp src/app/ide/main.spl --feature-check --tui
bin/simple-interp src/app/ide/main.spl --feature-check --gui
SIMPLE_LIB=src bin/simple-interp test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
simple spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

The docgen result must read like an operator manual and report `0 stubs`. The
final command must print `0`.
