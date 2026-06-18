---
name: ide-office
description: "Work on the Simple IDE Office plugin suite: markdown, slides, sheets, dashboard, DB admin, plugin manifests, and feature-check verification."
---

# IDE Office

Use this skill when a task changes `src/app/ide/` Office integration or the
Office apps under `src/app/office/` as they appear in the IDE.

## Scope

- IDE capability reporting: `src/app/ide/feature_report.spl`
- IDE TUI/GUI sanity checks: `src/app/ide/tui_sanity.spl`,
  `src/app/ide/gui_sanity.spl`
- IDE plugin metadata: `src/app/ide/plugin_manifest.spl`
- Markdown decoration: `src/app/ide/markdown_render.spl`
- Office apps: `src/app/office/slides/`, `src/app/office/sheets/`,
  `src/app/office/launcher.spl`
- Rendering guide: `doc/07_guide/app/ide_office_plugin_suite.md`
- System coverage:
  `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`

## Workflow

1. Keep IDE integration pure: feature checks must run without host GUI,
   browser, network, shell-out, or desktop APIs.
2. Update `feature_report.spl` when adding or renaming a capability that should
   be visible in `--feature-check`.
3. Keep TUI and GUI reports aligned; a feature should not appear in only one
   mode unless the spec documents why.
4. Update plugin manifest coverage when adding IDE-visible Office tools.
5. Add or update system assertions in
   `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`.
6. For Markdown WYSIWYG GUI work, keep `md_wysiwyg_gui.spl` on
   `wysiwyg_preview_document_html` so the CSS wrapper and escaped HTML path are
   the rendered product surface.
7. For slide/PPT render work, keep `slides/html_render.spl` pure and assert
   escaped text, sanitized colors, clamped geometry, and positioned slide boxes.

## Verification

Run the focused checks before handing off:

```bash
bin/simple-interp src/app/ide/main.spl --feature-check --tui
bin/simple-interp src/app/ide/main.spl --feature-check --gui
SIMPLE_LIB=src bin/simple-interp test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
find doc/06_spec -name '*_spec.spl' | wc -l
```

The final command must print `0`.

When changing Markdown/PPT rendering, also run the focused unit specs:

```bash
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/md_wysiwyg_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/md_wysiwyg_render_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/slides/html_render_spec.spl
```
