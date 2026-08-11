---
name: ide-office
description: "Work on the Simple IDE Office plugin suite: Markdown/Writer, Impress/PPT, Calc, Draw/SDD, Designer, Base, Math, Mail, Planner, dashboard, DB admin, plugin manifests, and feature-check verification."
---

# IDE Office

Use this skill when a task changes `src/app/ide/` Office integration or the
Office apps under `src/app/office/` as they appear in the IDE. Keep the guide
`doc/07_guide/app/ide_office_plugin_suite.md` current with user-visible Office
capsules, feature-check behavior, and plugin architecture rules.

## Scope

- IDE capability reporting: `src/app/ide/feature_report.spl`
- IDE TUI/GUI sanity checks: `src/app/ide/tui_sanity.spl`,
  `src/app/ide/gui_sanity.spl`
- IDE plugin metadata: `src/app/ide/plugin_manifest.spl`
- Markdown decoration: `src/app/ide/markdown_render.spl`
- Office apps: Markdown/Writer, Impress/PPT, Calc, Draw/SDD, Designer, Base,
  Math, Mail, Planner, dashboard, DB admin, and `src/app/office/launcher.spl`
- System coverage:
  `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`

## Workflow

1. Keep IDE integration pure: feature checks must run without host GUI,
   browser, network, shell-out, or desktop APIs.
2. Update `feature_report.spl` when adding or renaming a capability that should
   be visible in `--feature-check`.
3. Keep TUI and GUI reports aligned; a feature should not appear in only one
   mode unless the spec documents why.
4. Keep Office capsule wiring plugin-based: use manifest contributions,
   scoped DI service tokens, and declared AOP hooks instead of sibling-private
   imports.
5. Update plugin manifest coverage when adding IDE-visible Office tools.
6. Add or update system assertions in
   `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`.
7. For Calc TUI work, preserve the established `SheetsApp` viewport of 20
   columns by 30 rows. The canonical fixed evidence frame is 124x37 terminal
   cells (4 row-header columns + 20 cells x 6 columns, plus 7 chrome/status
   rows). A reduced preview such as 6x8 is a regression, and an empty
   re-export-module launch is not UI evidence.
8. Launch the executable owner (`src/app/office/mod.spl` or a compiled Office
   app artifact), not a module that only re-exports symbols. PTY verification
   must show the title, formula bar, full grid, sheet/status rows, and a
   non-empty independent capture.

## Verification

The raw-source IDE probes below diagnose capability ownership only. They do not
satisfy Calc CLI/TUI acceptance and must not regenerate its manual:

```bash
bin/simple-interp src/app/ide/main.spl --feature-check --tui
bin/simple-interp src/app/ide/main.spl --feature-check --gui
SIMPLE_LIB=src bin/simple-interp test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
simple spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

For Calc UI-access acceptance, use an observed pure-Simple self-hosted deployed
runtime. The SSpec invokes `--scenario all --run-id <unique>` exactly once and
shares only that fresh run across its visible workflow and folded error/NFR
scenarios:

```bash
SIMPLE_BINARY="$PWD/bin/simple" bin/simple test test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

Do not run Office acceptance or docgen through `bin/simple-interp`, a Rust seed,
raw Office source, or a shared prior evidence directory.

The generated manual at
`doc/06_spec/03_system/app/ide/feature/ide_office_plugin_suite_spec.md` must
read like an operator manual and report `0 stubs`. The final command must
print `0`.

For Calc UI changes, additionally assert the retained text capture is exactly
124 columns by 37 rows and contains visible cells from both ends of the
viewport (A1 and T30).
