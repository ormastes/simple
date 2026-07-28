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
- Manuals: 42 font mirrors (19 missing, 23 stale) plus four missing compiler
  prerequisite mirrors; every mirror needs immutable docgen and `0 stubs`.
- Evidence: REQ/NFR `0 pass / 0 active / 24 blocked`; AC
  `1 pass / 4 active / 7 blocked`.
- Checkout: 75 changed/new paths at `24a77be3c89a`; origin comparison is 87
  behind / 70 ahead. No completion sync has run.
- Source fixes cover per-invocation Stage3/HIR env/profile hoisting, GPOS
  owner-relative lookup, scalar owner-fault receipts, transactional atlas/fence
  safety, reusable vertex bytes, a bounded completed vertex pool, one deferred
  fallback snapshot, cleared Engine2D fallback pixels, stable Vulkan UUID/LUID
  identity, and wait/device-loss error retention.
- Host-independent exact Rust diagnostics pass: runtime UUID/LUID identity
  (0.00s, 5,632 KiB max RSS) and compiler device-loss classification (17.84s,
  2,169,768 KiB max RSS). They are not pure-Simple acceptance evidence.
- No admitted current-source CLI exists. Runtime, docgen, native, QEMU, and
  performance acceptance rows have not run; unavailable hardware is never PASS.
- Three producer/profile cycles are exhausted. This window permits no fourth
  producer or full bootstrap; a fresh window may resume the retained cache once.
- Exact NFR-007 blocker remains `font-owner-fault-runtime-proof-unavailable`.

## Open Next

- [full task matrix](shared_multilingual_gpu_fonts_all_items_2026-07-26.md)
- [verification report](../../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md)
- [bootstrap blocker](../../../08_tracking/bug/shared_font_stage4_stale_compiler_backfill_2026-07-26.md)
