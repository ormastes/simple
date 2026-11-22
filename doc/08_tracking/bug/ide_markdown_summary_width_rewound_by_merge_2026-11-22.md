# IDE feature-check markdown row rewound to 127 columns by merge e274cd33719 (2026-11-22)

Status: FIXED in source (this change). Found by the essential-apps Phase 1 check on
`release/1.0.0` @ `9c38b90cbe6`.

## Symptom

`test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`:

- "keeps the TUI feature-check layout within terminal width" — `expected 127 to be less than 121`
- "checks markdown rendering ..." — `expected markdown: ... to contain prev=`

## Root cause

`src/app/ide/markdown_render.spl` `ide_markdown_render_summary` had been shortened to
`prev=/head=/html_head=` keys (with a comment naming the 121-column budget). The
557-branch tournament merge `e274cd33719` brought back the older long form
(`preview=/heading=/html_heading=`), so the `  check: markdown:` row became 127 columns
wide. This is the stale-snapshot rewind class (`doc/07_guide/infra/vcs/stale_merge_snapshot_rewind.md`).

## Fix

Restore the abbreviated keys and the budget comment from `e274cd33719^`.

## Specs

- Reproducing: `test/01_unit/app/ide/ide_feature_check_width_spec.spl`
  "keeps the markdown summary abbreviated with the prev= key".
- Generalization: same file, "keeps every TUI and GUI feature-check row within 120
  columns" (covers every capability row in both modes).
- System: `ide_office_plugin_suite_spec.spl` width scenario now passes on Phase 1.

Verification (Phase 1 seed, interpreter): unit spec 2/2; system suite 19/21 (the two
remaining failures are `ide_feature_probe_placeholder_counts_2026-11-22.md`).
