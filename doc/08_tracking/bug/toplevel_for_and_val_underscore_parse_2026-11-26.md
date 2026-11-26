# Top-level `for` and top-level `val _ =` fail the full frontend (2026-11-26)

Status: open (verification-pending workaround in tests)

Found while fixing `test/01_unit/compiler/lint/lint_cli_*_contract_check.spl`
(`simple robust --source hir` exited 2 on that directory).

1. A top-level (module scope) `for x in expr:` statement: the flat AST bridge
   reports `unhandled expr node kind (tag=16)` (EXPR_FOR) at end of file via
   `convert_nodes.spl` `convert_flat_expr`. Inside a `fn` body the same loop
   parses.
2. A top-level `val _ = call(...)`: `expected Ident, got _ '_'` (line 38 of
   `lint_cli_argument_count_contract_check.spl`). Inside a `fn` body
   (e.g. `src/app/browser/render_adapter.spl:270`) `val _ =` parses.

Workaround applied: each of the 8 contract-check scripts now wraps its body in
`fn main():` and calls `main()`. Fix needed: handle EXPR_FOR in the flat AST
bridge at module scope, and accept `_` as a binding at module scope.

## Summary
- Bug A: module-scope `for` -> flat AST bridge `unhandled expr node kind (tag=16)`.
- Bug B: module-scope `val _ = ...` -> `expected Ident, got _`.
- Workaround (both): wrap the script body in `fn main():` plus a trailing `main()`.
  A separate lane owns the parser fix; remove the wrappers only if that is wanted.

## Open defects found while verifying (failed BEFORE the wrap too)
Run with the fresh seed `simple run`; before and after wrapping give identical exit code and output.
1. `lint_cli_argument_count_contract_check.spl`: rc=1, `FAIL: argument-count lint escaped its CLI owner or missed a threshold`.
2. `lint_cli_duplicate_typed_args_contract_check.spl`: rc=1, `FAIL: DTYP001 CLI ownership, call line, or config parity changed`.
3. `lint_cli_wide_public_contract_check.spl`: rc=1, `FAIL: W0404 CLI parity changed ...`.
4. `lint_cli_collection_dtyp_contract_check.spl`: rc=1, `method len not found on type nil` at line 96.
These may be seed-interpreter limits rather than lint bugs; not triaged. The files only had to parse for this change.

## Perf regression (recorded per CLAUDE.md)
With all files parsing under the default `--source hir`, on the fresh seed (interpreted, shared box):
- `robust inventory --sdn test/01_unit/compiler/lint`: returned 0 (completed).
- `robust boundaries test/01_unit/compiler/lint`: did NOT finish within 1700 s.
- `simple test test/01_unit/compiler/lint/bound_origin_facts_spec.spl`: child-timeout at the 900 s budget, twice, with no verdict.
### Profile (2026-11-27, seed `C:/dev/wt/bound3x-target/release/simple.exe`)
There is no superlinear term. In HIR mode `inventory --sdn` and `boundaries` share one code path (`_robust_render_hir`), so the "inventory returned" observation above came from another source or build.
- `boundaries` wall time for n files of the directory, text vs hir: n=1 16.0/26.0 s, n=2 15.8/40.3 s, n=4 15.9/48.4 s, n=8 14.1/101.4 s. Text mode is flat (startup only). Hir mode grows with total lines at ~0.07-0.09 s/line.
- Per phase, on synthetic files (50/100/200/400/800 lines): parse 10.6/21.1/42.7/85.2/170.7 s, lower 3.3/7.0/13.9/28.0/56.8 s. Both are exactly linear. `hir_origin_table_for_module` takes 4 ms per file.
- Cause: the robust module is demoted from the JIT to the interpreter (`[jit-fallback] Cannot infer field type: struct 'FileHandle' field 'mode' (declared fields: fd)`), so the pure-Simple frontend runs interpreted at ~0.2 s/line. That is 16k lines x 2 surfaces against a 900 s budget.
- Demotion trigger: `src/lib/nogc_async_mut/io/file.spl` declares `type FileHandle = AsyncFile` / `type File = AsyncFile` (AsyncFile has only `fd`). `std.nogc_async_mut.io` imports those names under "Sync implementations", and the gc twin re-exports the sync class. Re-exporting the sync class removes this demotion but exposes (1) a private `hir_phase_memo_promote_roots` imported by two modules (fixed in this change: now `pub`) and (2) a seed SEGV (rc=139) once the frontend is JIT-admitted. So the alias change is held back.
- The parse cache (`frontend_parse_or_restore`, xxh3 key) does not hit across runs for `robust_hir`: file 1 cost ~10 s in every run.
- Spec fix: `bound_origin_facts_spec` walks the large directory with `--source text` and covers the HIR default on `fixtures/bound_graph` (42 lines).

TODO(seed, P2): fix the `FileHandle`/`File` = `AsyncFile` alias collision in `src/lib/nogc_async_mut/io/file.spl` together with the seed SEGV it exposes once the frontend is JIT-admitted (repro: re-export `std.nogc_sync_mut.io.file.{FileHandle, File}` there, then run `run_robust(["boundaries", "--source", "hir", <one file>])` on the seed -> rc=139). Then re-measure on a pure-Simple binary.

## Root causes and fix (added 2026-11-26)
- Bug A: `convert_flat_expr` in `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` had no case for EXPR_FOR / EXPR_WHILE (tags 16 / 17), so module-scope loops were reported as unhandled.
- Bug B: module-level `parse_val_decl` in `src/compiler/10.frontend/core/parser_decls_use.spl` rejected the `_` token (kind 169).
- Fix: PR #12041, `71e6065cf88`, status verification-pending (not natively verified).
- The `fn main()` wrap in the 8 scripts is kept as defensive code (reverting would need re-verifying all 8 scripts).

## Open gap / todo
TODO(parser, P3): module-scope tuple destructuring `val (a, _) = ...` is not supported; add support and a spec.
