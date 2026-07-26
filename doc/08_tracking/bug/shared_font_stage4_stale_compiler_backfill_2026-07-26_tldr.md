# Shared-Font Stage 4 Stale Compiler Backfill — TLDR

Stage 2/3 are retained, but no Stage 4 CLI exists. Explicit enums and GPOS now
parse. HEAD `7a161abfabb` fixes impl-only bootstrap accumulation; the final
cycle-3 check advanced `compiler.spl` from zero to 15 retained functions and
localized the remaining nil receiver inside HIR error collection. The
typed-index collector fix and direct regression are implemented but
bootstrap-unverified. The three-check cap is exhausted.

## Core Shape

- directory symlink source snapshots now pass with regression coverage;
- `pub mod` now uses the shared module parser path with a focused spec;
- the GPOS grammar blocker is cleared;
- explicit enum discriminants and impl-only function accumulation are
  implemented with direct regressions;
- the final markers are `driver:errors-read:done` followed by the nil receiver;
- HIP-to-ROCm batches, fail-closed degenerate Web, and nested IMAGE projection
  are source-complete but unverified;
- retained Stage 2/3 and native caches must be preserved;
- do not use the Rust seed or stale CLI as evidence.

## Open Next

- run the exact cache-preserving command in the full blocker doc only in a
  fresh continuation and require exit 0;
- then run the impl-accumulator and typed-error-collector regressions before
  any font evidence;
- [full blocker and exact resume command](shared_font_stage4_stale_compiler_backfill_2026-07-26.md)
- [all-items verification](../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md)
