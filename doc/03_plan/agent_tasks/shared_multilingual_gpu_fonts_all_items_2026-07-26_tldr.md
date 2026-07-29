# Shared Multilingual GPU Fonts — All Remaining Items — TLDR

Six non-overlapping lanes own REQ-001–016 and NFR-001–008; `/root` integrates,
reviews, syncs, and pushes.

## Core Shape

- P0 admits the pure-Simple CLI/core-C identity; A runs shared calibration.
- B distribution, C shaping/material/config, D host rows, and E deterministic
  native/performance evidence proceed independently.
- Owners generate manuals, F audits them, and H performs the final review/sync.
- `FontRenderer`/`FontRenderBatch`, SSpec steps, and checker names are frozen.

## Current Truth

- Focused graph: 46 commands (preflight, B6, C18, D12, E9).
- Manuals: 42 font mirrors (0 current, 19 missing, 23 stale) plus four missing
  compiler-prerequisite mirrors; every canonical mirror needs immutable docgen
  and `0 stubs`. Diagnostic manuals under `build/test-artifacts/` are noncanonical.
- Evidence: REQ/NFR `0 pass / 0 active / 24 blocked`; AC
  `1 pass / 4 active / 7 blocked`.
- Checkout: HEAD and the pushed checkpoint are `502b70b5460` (0 ahead/0 behind);
  `origin/main` is `dcc5328864d5`, with HEAD 82 ahead and 467 behind main.
- Stage2 successor3 `dd7e747a…26cf` reused 689 modules and rebuilt four; that
  incremental receipt is diagnostic only. The capped Option smoke ended in
  nil/SIGILL, produced no Stage4 CLI, and must not be promoted or repeated.
- Source audits justify no new product code before one admitted current-source
  pure-Simple CLI/core-C supplies runtime evidence. Runtime, canonical docgen,
  native, QEMU, and performance acceptance remain open.
- Unavailable hardware rows remain explicitly blocked, never skipped or PASS.
- Exact NFR-007 blocker remains `font-owner-fault-runtime-proof-unavailable`.

## Open Next

- [full task matrix](shared_multilingual_gpu_fonts_all_items_2026-07-26.md)
- [verification report](../../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md)
- [bootstrap blocker](../../../08_tracking/bug/shared_font_stage4_stale_compiler_backfill_2026-07-26.md)
