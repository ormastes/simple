# Pure-Simple parser: `pub unit` rejected; `@when(...):` reaches parser in stage2c

Status: verification-pending (2026-11-17)

## Symptoms (phase-3 stage2c parse of src/lib)
1. `pub unit FreeBytes: i64 as fbytes` -> `expected declaration after visibility modifier`.
2. `@when(os="windows"):` (top level and indented in fn bodies, e.g.
   `src/lib/nogc_sync_mut/sffi/process_memory.spl:64`,
   `src/lib/common/io/read_only_file_view.spl:239`) -> `unexpected token in expression: ':'`.

## Root cause / fix
1. `parse_module_decl_with_visibility`
   (`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`) had no
   `unit` arm. The `unit` body is now one helper
   (`parse_unit_decl_after_keyword_v1`) used by the plain and visibility paths;
   the visibility path stamps the visibility on the lowered struct decl. The
   Rust seed accepts `pub unit`. FIXED.
2. NOT a grammar gap. The seed masks `@when` in its lexer
   (`src/compiler_rust/parser/src/cond_compile.rs`); pure-Simple blanks directive
   lines in `_pp_preprocess_conditionals`, which every parse entry calls
   (`parser.spl` parser init / `parse_module_silent_checked`). Under the
   interpreter the same shapes parse cleanly (spec below, green before any
   change). So the stage2c failure is native-only: the native preprocessor
   leaves directive lines in place, or stage2c was built from a stale
   producer. OPEN — next step: run the spec's sources through stage2c's
   `_pp_preprocess_conditionals` and diff; likely suspects are native
   `text[i] == "("` char/text compares in `_pp_extract_paren_condition`
   and the `_pp_may_have_conditionals` short-circuit.

## Specs
- Repro + generalization: `test/01_unit/compiler/frontend/parser_when_block_and_pub_unit_spec.spl`
  (pub unit red before fix, 4/4 green after; `pub(package)` / suffix-less /
  derived `pub unit` variants; @when top-level, @else+nested @when, in-fn).
- Regression: `test/01_unit/compiler/frontend/unit_decl_canonical_spec.spl` 10/10.
