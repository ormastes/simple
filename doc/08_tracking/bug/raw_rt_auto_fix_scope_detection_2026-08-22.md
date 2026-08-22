# Raw runtime lint auto-fix scope detection

Status: open, pre-existing; isolated while adding lexical FFI containment.

`test/01_unit/compiler/lint/raw_rt_access_spec.spl` has four failures on the
current bootstrap test lane that are independent of tagged declarations and
lexical `unsafe(ffi)` blocks:

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

Fix the import-scope recognizer and align the file-read diagnostic with the
deliberately non-mechanical mapping. Do not add a bare file-read rename: its
nullable/error semantics vary across existing facades.
