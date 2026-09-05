# MC/DC-wrapped spec copy fails semantic analysis with `undefined identifier: fs` (directory targets only)

- **Status:** OPEN
- **Found:** 2026-09-02, Windows (bin/simple.exe, md5 `d52d770724a9f8797e98ac7819709ab9`)
- **Visible only after:** the observed-ABI fallback fix and the coverage-wrapper
  path-flattening fix. Before those, every directory-target spec aborted earlier
  with an empty `Compilation failed:` message, so this class was invisible.

## Symptom

`bin/simple test test/00_formal_verification` (DIRECTORY target, which enables
MC/DC and therefore forces the native standalone-SMF compile path) fails 11 spec
files that pass when the same files are named explicitly:

| mode | Results |
|---|---|
| directory | `118 total, 107 passed, 11 failed` |
| explicit files (23 summaries, aggregated) | `174 total, 171 passed, 3 failed` |

All 11 share ONE diagnostic shape, taken from the wrapped+relocated copy under
the temp dir:

```
error: compile failed (<TMP>/spipe_wrapped_<TMP>_simple_cov_test_00_formal_verification_compiler_lean_codegen_spec_spec_native.spl):
  semantic: ...: Undefined("undefined identifier: fs")
```

`tool_checker_spec.spl` reports `undefined identifier: regen` instead; same shape.

Offenders: `deterministic_emission_spec.spl`, `lean_block_integration_spec.spl`,
`lean_codegen_spec.spl`, `lean_package_root_import_spec.spl`,
`lean_package_root_similar_symbols_spec.spl`, `lean_workflow_spec.spl`,
`regeneration_spec.spl`, `regeneration_theorem_emission_class_spec.spl`,
`toolchain_detection_spec.spl`, `tool_checker_spec.spl`,
`verification_std_api_generalization_spec.spl`.

Note `fs` / `regen` are NOT named in the spec sources; they come from the
imported `verification.*` modules. The identifier resolves fine when the spec is
run in place and only fails for the copy relocated into the temp dir.

## Why the existing degrade path does not catch it

`run_test_file_native` degrades a failed instrumentation compile to a plain
interpreter run only when the diagnostic contains the literal string
`"cannot compile to standalone SMF"`
(`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`, `uncompilable_construct`;
twin at `src/app/test_runner_new/test_runner_execute.spl:539`). A semantic
`Undefined(...)` from the wrapped copy does not match, so the spec is reported as
a compile failure.

## Do NOT "fix" this by widening the trigger

Broadening `uncompilable_construct` to any semantic failure of the wrapped copy
would degrade-to-interpreter on GENUINE compile errors too, masking real defects
— the same class of diagnostic destruction that produced the empty
`Compilation failed:` message. The correct fix is to make the relocated wrapper
resolve the same identifiers the original does (or to compile the wrapper in
place), not to widen the escape hatch.

## Unblock condition

The wrapped/relocated copy must resolve module-provided identifiers identically
to the in-place source. Re-verify by running
`bin/simple test test/00_formal_verification` as a directory and requiring its
aggregate to match the explicit-file aggregate (currently 171/174; 3 of those are
genuine RED in `lean_codegen_spec.spl` and `lean_workflow_spec.spl` and are a
separate matter).

## Related

- `src/lib/nogc_sync_mut/io/resource_scope.spl` — observed-ABI fallback
  (`_legacy_bounded_fallback`, `_receipt_shows_no_child`); Windows ENOTSUP is 129.
- `src/app/test_runner_new/test_executor_parsing.spl` and its lib twin —
  coverage-wrapper temp-path flattening.
- Specs: `test/01_unit/lib/io/resource_scope_observed_abi_fallback_spec.spl`,
  `test/01_unit/lib/io/resource_scope_fallback_does_not_mask_failures_spec.spl`,
  `test/01_unit/lib/test_runner/coverage_wrapper_path_flattening_spec.spl`.
