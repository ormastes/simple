# `load_sdoctest_blocks` / `compute_sdoctest_coverage` are re-exported and called but never defined

**Date:** 2026-07-28 · **Status:** open · **Class:** NEVER-EXISTED (capability gap)
**Found:** triage of `scripts/check/check-dangling-references.shs` findings scoped
to `src/app/cli/**`.

## Symptom

```
src/app/cli/doc_coverage_command.spl:8: SYMBOL: imported name `compute_sdoctest_coverage` is declared in no src file
src/app/cli/doc_coverage_command.spl:8: SYMBOL: imported name `load_sdoctest_blocks` is declared in no src file
```

## Referencing sites

`src/app/cli/doc_coverage_command.spl:8`

```spl
use app.doc_coverage.analysis.sdoctest_coverage.{load_sdoctest_blocks, suggest_missing_tags, compute_sdoctest_coverage}
```

Call sites in the same file:

| Line | Call |
|---|---|
| 75  | `val sdoctest_result = load_sdoctest_blocks()` |
| 95  | `val coverage = compute_sdoctest_coverage(all_items, sdoctest_blocks)` |
| 148 | `val blocks_result = load_sdoctest_blocks()` |
| 338 | `val blocks_result = load_sdoctest_blocks()` |

## Missing targets

`src/app/doc_coverage/analysis/sdoctest_coverage.spl` exists but declares only:

```
validate_tag_format, _basename_without_ext, suggest_missing_tags,
_decl_name_after_prefix, extract_function_names_from_code,
match_functions_to_sdoctest
```

Neither `load_sdoctest_blocks` nor `compute_sdoctest_coverage` is there.
`suggest_missing_tags` — the third name on the same import line — *is* there,
which is why only two of the three are flagged.

Worse, the package barrel promises them anyway.
`src/app/doc_coverage/analysis/mod.spl:13,16`:

```spl
export load_sdoctest_blocks
export compute_sdoctest_coverage
```

Those `export` statements name functions that no file in the package defines —
so the barrel advertises an API surface it cannot supply.

## Not a rename

The nearest existing name is
`src/app/doc_coverage/analysis/group_sdoctest.spl:281`:

```spl
fn load_sdoctest_blocks_for_module(module_path: text) -> [text]
```

This is **not** a safe repoint: it takes one `text` argument and returns
`[text]`, whereas every call site calls `load_sdoctest_blocks()` with zero
arguments and then reads fields off the result (`sdoctest_result`,
`blocks_result`). Different arity and different return shape. Repointing the
import would convert a resolution error into a wrong-arity error, so it was
left alone.

`compute_sdoctest_coverage` has no near-name analogue at all.

## Consequence

`src/app/cli/doc_coverage_command.spl` is the CLI backing for
`bin/simple doc-coverage`. Its sdoctest-coverage paths (four call sites) cannot
resolve. Any consumer of `app.doc_coverage.analysis` that trusts the barrel's
`export load_sdoctest_blocks` / `export compute_sdoctest_coverage` inherits the
same break.

## Not fixed here

Needs an owner to either implement the two functions in
`analysis/sdoctest_coverage.spl` (matching the zero-arg + result-object shape
the four call sites assume), or remove the two `export` lines from
`analysis/mod.spl` and rework the four call sites. Not guessed at here.
