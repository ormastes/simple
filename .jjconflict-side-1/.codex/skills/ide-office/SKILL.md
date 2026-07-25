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

## Verification

Run the focused checks before handing off:

```bash
bin/simple-interp src/app/ide/main.spl --feature-check --tui
bin/simple-interp src/app/ide/main.spl --feature-check --gui
SIMPLE_LIB=src bin/simple-interp test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
simple spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

The generated manual at
`doc/06_spec/03_system/app/ide/feature/ide_office_plugin_suite_spec.md` must
read like an operator manual and report `0 stubs`. The final command must
print `0`.
