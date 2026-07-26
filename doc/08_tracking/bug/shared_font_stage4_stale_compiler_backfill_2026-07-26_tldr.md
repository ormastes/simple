# Shared-Font Stage 4 Stale Compiler Backfill — TLDR

Three bounded attempts produced no admissible CLI. The fail-closed bootstrap
requires one fresh `--full-bootstrap --full-cli` run before font evidence.

## Core Shape

- deployed CLI is Rust-built and rejected by essential-tools admission;
- isolated provenance now passes after removing a worktree-only symlink input;
- final attempt stopped before Stage 2 because stale backfill requires `--full-bootstrap`;
- do not use the Rust seed, stale CLI, or a fourth unchanged retry as evidence.

## Open Next

- [full blocker and exact resume command](shared_font_stage4_stale_compiler_backfill_2026-07-26.md)
- [all-items verification](../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md)
