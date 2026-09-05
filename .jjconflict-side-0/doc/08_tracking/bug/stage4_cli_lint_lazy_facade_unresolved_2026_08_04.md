# Stage 4 CLI lint lazy-facade names are unresolved

## Status

Fixed in the LLVM 23.1 Stage 4 bootstrap lane on 2026-08-04.

## Symptom

After the full CLI closure parsed all 1,351 module surfaces, HIR lowering of
`src/app/io/cli_lint_commands.spl` failed on `check_simd_opportunities` and
`easyfix_id_text`.

## Root cause

The CLI imported both names through the lazy `compiler.tools.fix.rules`
facade. The SIMD checker is physically owned by `rules.impl_.lint_simd`, while
the text adapter followed a two-hop facade chain whose intermediate
`impl_/__init__.spl` did not export it. Stage 4 correctly failed closed instead
of inventing a callable owner. The adapter also duplicated the canonical
`easyfix_id` and `easyfix_description` accessors already owned by
`std.tooling.easy_fix.types`.

## Fix and regression

The consumer imports the SIMD checker directly from its physical lazy owner,
keeps only the short-grammar rule on the rules facade, and uses the canonical
EasyFix accessors from the types owner. The duplicate EasyFix facade import is
removed. `stage4_cli_lint_hir_contract.spl` imports and executes the real CLI
lint handler so native entry-closure lowering must resolve the complete body.
