# IDE feature-check probes report placeholder line counts (2026-11-22)

Canonical id: `ide_feature_probe_placeholder_counts_2026_11_22`
Status: OPEN. Specs intentionally left RED. Workaround markers added (this change).

## Symptom

`test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` on the Phase 1 seed:

- line 422-423 "checks markdown rendering through the shared editor renderer and preview
  pane": `expected 2 to be greater than 2`, `expected 0 to be greater than 2`.
- line 449 "checks TUI preview and outline panels": `expected 1 to equal 2`.

## Root cause

The probes do not call the renderer they claim to check; they return constants:

- `src/app/ide/markdown_render.spl` `ide_markdown_render_probe`:
  `rendered_line_count: 2`, `preview_line_count: 0`. The comment says Phase 3 "cannot
  safely pass this inline aggregate through the block renderer ABI" (a `BlockModel`
  across a function boundary), so the probe uses only `md_render_inline`.
- `src/app/ide/tui_sanity.spl` `ide_tui_sanity`: `outline_line_count: 1`.

The spec is correct; the implementation is a placeholder. Both sites now carry
`@workaround bug=ide_feature_probe_placeholder_counts_2026_11_22`.

Workaround commit: `fix(ide): restore 120-column markdown feature-check row; tag placeholder
probe counts` on `work/essential-apps-p1p2-20261122` (PR #10797). The markers tag pre-existing
placeholder code; no intended-code recovery reference exists. Bug DB reconciliation pending
(no qualified full-CLI `simple check-dbs` on this host).

## Unblock condition

Call `preview_pane_update` / `preview_pane_render` (`src/lib/editor/view/preview_pane.spl`)
and the slide-outline renderer for real counts once a native build of `src/app/ide/main.spl`
passes a `BlockModel` across a function boundary correctly. Verify by building the IDE
with the next compiler generation and running the system suite. Then remove both markers.
