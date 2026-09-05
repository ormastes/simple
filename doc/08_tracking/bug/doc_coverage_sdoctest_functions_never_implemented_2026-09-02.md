# `doc-coverage` calls `load_sdoctest_blocks` and `compute_sdoctest_coverage`, which are defined nowhere

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
