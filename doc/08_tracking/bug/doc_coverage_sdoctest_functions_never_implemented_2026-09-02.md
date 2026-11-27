# `doc-coverage` calls `load_sdoctest_blocks` and `compute_sdoctest_coverage`, which are defined nowhere
## Obsolete 2026-09-16 — dupe of doc_coverage_command_broken_missing_load_sdoctest_blocks_2026-09-05.md (same missing fns, grep-verified)

Reviewed in the 2026-09-16 bug-ledger normalization pass. Kept for history;
the subject is removed, superseded, or duplicated elsewhere in the ledger.

- Date: 2026-09-02
- Status: OPEN
- Severity: high (the command cannot complete a run)
- Binary: `bin/simple.exe`, md5 `d52d770724a9f8797e98ac7819709ab9`

## Measured

After the discovery fix in `3d2908f9455` (which removed a false
"No source files found" bail), `bin/simple.exe doc-coverage` gets further and
then fails:

```
error[E1002]: function `load_sdoctest_blocks` not found
  = help: check the function name or import the module that defines it
```

exit 1.

`src/app/cli/doc_coverage_command.spl:9` imports both names from
`app.doc_coverage.analysis.sdoctest_coverage`:

```
use app.doc_coverage.analysis.sdoctest_coverage.{load_sdoctest_blocks, suggest_missing_tags, compute_sdoctest_coverage}
```

That module defines `validate_tag_format`, `_basename_without_ext`,
`suggest_missing_tags`, `_decl_name_after_prefix`,
`extract_function_names_from_code`, `match_functions_to_sdoctest` — and neither
imported name. A tree-wide search finds **no definition of
`load_sdoctest_blocks` or `compute_sdoctest_coverage` anywhere**; the nearest
thing is `load_sdoctest_blocks_for_module` in
`src/app/doc_coverage/analysis/group_sdoctest.spl:281`, a different signature.

`load_sdoctest_blocks` is called at 4 sites (`:76`, `:96` via its result, `:149`,
`:339`).

## Second, independent defect in the same file

The module is dropped to the interpreter on every run:

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'DocItem' field 'file'
  (declared fields: name, kind, file_path, line, col, visibility, signature,
   has_inline_comment, has_docstring, has_sdoctest, is_public, is_exported)
  [in src/app/cli/doc_coverage_command.spl]
```

There are two `DocItem` structs. The one imported from
`app.doc_coverage.scanner.mod` has a `file` field; the one the command's code is
written against has `file_path`/`col`/`visibility`/`signature`. The file is a
half-finished migration.

## Do not stub

These are unimplemented features, not a wiring bug. Making `load_sdoctest_blocks`
return an empty list would produce a `doc-coverage` that exits 0 and reports
coverage numbers derived from no sdoctest data at all — a tool that reports
success without doing its job. Implement the two functions against the real
sdoctest block format, or delete the sdoctest arms of the command.


## 2026-11-10 triage (P3 runner2 lane, work/p3-runner2-20261110): SUPERSEDED dupe — both defects resolved

This doc was already marked obsolete 2026-09-16 as a dupe of
`doc_coverage_command_broken_missing_load_sdoctest_blocks_2026-09-05.md`.
On this base (origin/release/1.0.0) both of its defects are now resolved:

1. Missing `load_sdoctest_blocks` / `compute_sdoctest_coverage`: defined at
   `src/app/doc_coverage/analysis/sdoctest_coverage.spl:96,135` (landed
   with merge 9e7e7a526edb, PR #7597). Not stubs: the loader scans README +
   doc/*.md + doc/07_guide for fenced sdoctest blocks and the coverage
   function aggregates per-file and overall counters against them.
2. Two-`DocItem`-struct migration break (`class DocItem has no field named
   has_inline_comment`): FIXED in this lane — see the 2026-11-10 triage
   append in the dupe doc for the migration + evidence.

The "Do not stub" requirement is honored: no empty-list stub was added;
the real implementations (which postdate this doc) are what run.

Seed-smoke evidence (Rust seed `bin/simple.exe`, this worktree):
`bin/simple.exe doc-coverage` -> exit 0 with a real report over 9233 files
(75323 items, 41% documented, 11% sdoctest); the second defect's
`jit-fallback` on doc_coverage_command.spl (struct 'Nil' field 'items')
still demotes the module to the interpreter, but the run completes.
