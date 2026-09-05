# Raw runtime lint auto-fix scope detection

Status: fixed in source; deployed Pure-Simple CLI acceptance pending.

The original bootstrap lane exposed four failures independent of tagged
declarations and lexical `unsafe(ffi)` blocks:

- the file-read diagnostic expects `simple lint --fix`, although
  `raw_rt_wrapper_replacement` deliberately has no file-read mapping;
- both `app.io.mod.{process_run}` auto-fix cases produce no replacement;
- the `std.io_runtime.{process_run}` auto-fix case produces no replacement.

The new tagged-declaration, contained-call, and uncontained-call examples all
pass. The raw-lint performance contract also passes. Reproduce with:

```sh
bin/simple test test/01_unit/compiler/lint/raw_rt_access_spec.spl \
  --mode=interpreter --verbose
```

The source repair now requires an exact selective import and an unshadowed
wrapper binding. It offers signature-preserving fixes for `rt_process_run`,
`rt_remove`, and all four `rt_readdir*` operations. It deliberately withholds
bare file-read and `rt_mkdir` renames because their contracts require a semantic
choice. `test/02_integration/compiler/raw_rt_lint_cli_fix_test.shs` covers real
`simple lint --fix` file mutation once a deployed Pure-Simple runtime exists.
