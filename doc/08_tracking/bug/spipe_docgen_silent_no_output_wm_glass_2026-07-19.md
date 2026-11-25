# Bug: SPipe Docgen Exits Successfully Without Producing Manual
## Fixed 2026-11-25 — output-existence postcondition added to the docgen CLI

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## 2026-11-25 resolution

- **fix:** `src/app/spipe_docgen/spipe_docgen/main.spl` now treats a
  `generate_feature_doc_semantic_v1` `Ok(path)` whose file is missing as an
  error: it prints `docgen reported success but produced no manual: <path>`,
  marks the run failed, and the CLI exits nonzero (`had_error` -> return 1).
  Write failures already propagated (`native_fs_write_string` returning false
  becomes `Err` -> `had_error` in `publish_semantic_docgen_v1`); this closes
  the remaining silent-success-with-no-artifact hole at the CLI, which is the
  postcondition this doc's reproduction notes asked for.
- **contributing cause already fixed elsewhere:** the original exit-0-no-output
  run went through the Rust-seed `bin/simple spipe-docgen` subcommand route,
  which dropped argv; that is tracked and worked around in
  `doc/08_tracking/bug/spipe_docgen_subcommand_argv_drop_2026-08-16.md`
  (`args_from_proc_cmdline` fallback in `main()`).
- **verification limit:** runtime verification is blocked on this host —
  release/1.0.0 HEAD is source/binary inconsistent (the pinned seed rejects
  `@representation_boundary` in `src/lib`, so no docgen invocation can run at
  HEAD). Verified by code inspection: the postcondition sits on the only `Ok`
  path between generation and the summary/exit-code computation, and both
  `spipe_err` and `native_fs_exists` are already in scope in that function.
- The mirrored manual
  `doc/06_spec/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.md`
  now exists in-tree.

## Observed

On 2026-07-19, this command completed with exit status 0 after emitting a large
set of unrelated compiler warnings:

```text
bin/simple spipe-docgen test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl --output doc/06_spec --no-index
```

The required mirrored file was not created at
`doc/06_spec/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.md`
or elsewhere under `doc/06_spec`.

## Expected

Docgen should either create the mirrored manual and print its path/stub count,
or exit nonzero with a focused parse/generation diagnostic. Exit 0 with no
artifact is unsafe because verification can mistake it for successful manual
generation.

## Reproduction Notes

The source spec exists and uses established `@manual`, `@capture`, `@inline`,
`step(...)`, and module-doc conventions. The command was run once and was not
repeated because identical retry loops are prohibited. Investigation should
first add an output-existence postcondition to the docgen CLI.

## Impact

Blocks generation of the WM glass theme system manual until fixed or until a
different canonical docgen invocation is identified. It does not justify a
hand-written manual being represented as generated evidence.

