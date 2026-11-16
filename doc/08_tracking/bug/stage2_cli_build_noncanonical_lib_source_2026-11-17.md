# Stage 2 `compiler_cli_build` rejects four non-canonical lib sources (2026-11-17)

- **Status:** verification-pending. The fix has landed, but no native Stage 2 run has confirmed it yet.
- **Lane:** release/1.0.0, Stage 2 compiler tests (WSL Ubuntu-24.04, pin `ca03d60c15a`).

## Symptom

In the Stage 2 compiler tests, the `compiler_cli_build` row failed with `FAIL status=1` after 1770 s. The cause was three parse errors from the self-hosted parser:

```
parse error in src/lib/nogc_sync_mut/io/linux_fresh_epoch_population_v1.spl: 194:47:expected Ident, got IntLit '0'
parse error in src/lib/nogc_sync_mut/orchestration/host_runtime_exec_projection_v3.spl: 45:13:unexpected token in expression: : ':'
parse error in src/lib/nogc_sync_mut/orchestration/host_runtime_exec_no_begin_cancel_evidence_v3.spl: 42:13:unexpected token in expression: : ':'
```

## Root cause

The defect is in the source, not the grammar. Both constructs are outside the documented language.

1. **`f()?.0`.** `?.` is optional chaining (safe navigation). The documented spelling for try-then-access is `(x?).field`; see the comment at the `?.` branch in `parser_expr.spl`. The lexer emits `?.` as a single token, `QUESTION_DOT`, so the token after it must be an identifier. The Rust seed's `expect_method_name` also accepts only identifiers and keywords there. These lines were meant as a try, so the optional-chain reading would also have swallowed the `Err`.
2. **`else:` at the then-body's indentation inside `val x = if c:`.** The canonical multi-line if-expression puts `else:` at the indentation of `val`. A tree scan found 1571 canonical sites and exactly 4 with an inline `else:` at body indentation. All 4 are in the two orchestration v3 files.

A whole-tree scan found 2 `)?.<digit>` sites, both in `linux_fresh_epoch_population_v1.spl`, plus the 4 `else:` sites. The CLI build reports only the first error in each file, so it showed 3 errors for these 6 sites.

## Fix

- Rewrote the two try sites as `(population_meta_v1(...)?).0`.
- Moved the four `else:` lines out to the indentation of `val`.
- The grammar is unchanged; the owner decided this on 2026-11-17.

## Regression test

`test/01_unit/compiler/frontend/stage2_lib_source_parses_spec.spl` parses each file through `compiler.core.parser.parse_module_silent_checked`. That function returns the failure flag by value. The `parse_module` + `parser_has_errors` pair is not reliable across the module boundary; see `parser.spl`.

Against the source as it was before the fix, all 3 cases fail. With the fix, all 3 pass. The spec also asserts that no `)?.0` or `)?.1` spelling remains.

## Verification still needed

Rerun the Stage 2 compiler tests on a commit that includes this fix. `compiler_cli_build` must get past these files.

The `test_runner_build` row is still blocked by a separate bug: `named call lacks bootstrap parameter metadata`. That is the owner-lane bug recorded in `d06ba38f018`, and it is not addressed here.
