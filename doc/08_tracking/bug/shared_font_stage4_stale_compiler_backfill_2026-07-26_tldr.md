# Shared-Font Stage 4 Stale Compiler Backfill — TLDR

Final retry 3 admitted Stage 2/3 but produced no Stage 4 CLI. GPOS parsing
cleared; Stage 4 first failed on explicit enum value `Exit = 0` in
`src/os/kernel/types/syscall_types.spl:8`. The hard retry cap is exhausted.

## Core Shape

- directory symlink source snapshots now pass with regression coverage;
- `pub mod` now uses the shared module parser path with a focused spec;
- the GPOS grammar blocker is cleared;
- pure enum parsing/flat AST/typed variants do not preserve explicit numeric
  discriminants, so skipping `= N` would corrupt syscall ABI values;
- retained Stage 2/3 and native caches must be preserved;
- do not use the Rust seed or stale CLI as evidence.

## Open Next

- implement end-to-end explicit discriminant preservation plus a focused
  non-sequential `SyscallId` regression, or obtain an architectural CLI-closure
  exclusion;
- rerun the exact cache-preserving command in the full blocker doc only in a
  fresh continuation;
- [full blocker and exact resume command](shared_font_stage4_stale_compiler_backfill_2026-07-26.md)
- [all-items verification](../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md)
