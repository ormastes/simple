# Simple Seed Loader Restart Plan - 2026-06-01

## Goal

Resume the segfault/loader hardening work with Rust treated only as the seed/tooling binary. Fix the Simple implementation path first.

## Current State

- Default `bin/simple` had previously been confirmed as the deployed pure Simple bootstrap.
- Rust-side hardening exists from the interrupted parent thread, but it should be treated as seed/tooling guardrail work, not the main fix.
- Simple-side guard work was started in:
  - `src/compiler/70.backend/linker/lld_sffi.spl`
  - `src/lib/nogc_sync_mut/sffi/llvm_loader.spl`
  - `src/lib/nogc_sync_mut/sffi/llvm_target.spl`
  - `src/lib/nogc_sync_mut/sffi/llvm_types.spl`
  - `src/lib/log.spl`
  - `src/compiler/99.loader/loader/smf_mmap_native.spl`
  - `src/compiler/70.backend/linker/smf_reader_memory_part1.spl`
  - `src/compiler/70.backend/linker/smf_reader_memory_part2.spl`
  - `src/compiler/80.driver/smf_writer.spl`
  - `src/compiler/99.loader/loader/module_loader.spl`
  - `src/compiler/99.loader/module_loader.spl`
- Temporary debug files under `build/tmp/` were deleted before this restart note.

## Known Findings

- `test/01_unit/compiler/loader/module_loader_relocation_spec.spl` still fails.
- The failure is not resolved by the partial layout fixes yet.
- Diagnostic work indicated:
  - Simple SMF writer/reader layout assumptions were inconsistent.
  - The in-memory reader needed 64-byte section table entries.
  - The Simple writer symbol entry needed to align with the documented 56-byte symbol layout.
  - Header parsing in `smf_reader_memory_part1.spl` was reading offsets as if there were extra repr(C) padding, but `smf_header.spl::to_bytes()` writes packed fields.
  - The compatibility `compiler.loader` facade path can return a successful load with zero symbols.
  - A separate parse blocker exists in `src/compiler/10.frontend/flat_ast_bridge_part2.spl`: `Unexpected token: expected expression, found Else`.

## Restart Steps

1. Inspect current diffs before editing; preserve unrelated dirty work.
2. Re-run focused lint on the Simple files touched above.
3. Decide whether the partial compatibility-loader changes in `src/compiler/99.loader/module_loader.spl` should be completed or reverted in favor of fixing the newer `src/compiler/99.loader/loader/module_loader.spl` path.
4. Fix the SMF layout contract in one place:
   - section table entry size
   - symbol entry size
   - symbol type/binding values
   - header byte offsets
   - string table offset calculation
5. Fix the compatibility loader returning success with zero symbols.
6. Re-run:
   - `src/compiler_rust/target/bootstrap/simple lint <focused Simple files> --json`
   - `src/compiler_rust/target/bootstrap/simple test test/01_unit/compiler/loader/module_loader_relocation_spec.spl --mode=interpreter --clean`
   - `src/compiler_rust/target/bootstrap/simple test test/01_unit/lib/log_lite_ring_spec.spl --mode=interpreter --clean`
7. Confirm `bin/simple --version` still resolves to the pure Simple deployed bootstrap.
8. Confirm `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Important Constraint

Do not continue expanding Rust fixes unless required for seed/tooling diagnostics. The product fix belongs in Simple code.
