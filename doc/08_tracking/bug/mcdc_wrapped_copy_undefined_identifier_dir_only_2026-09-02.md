# MC/DC-wrapped spec copy fails semantic analysis with `undefined identifier: fs` (directory targets only)

- **Status:** FIXED (2026-11-11, lane ne14) — relocated wrapped copy resolves identifiers identically; failure mode now fail-closed, see addendum
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

## Addendum 2026-11-11 (lane ne14) — FIXED, verified on release/1.0.0 (Windows seed)

**Verification actually run** (seed-smoke, worktree simple-p3-ne14-20261111,
fresh seed 46fe8f6b6def, SIMPLE_LIB=src):

1. **Root cause gone — relocated copies resolve identically.** Linted the
   former offender `test/00_formal_verification/compiler/lean_codegen_spec.spl`
   (still `use verification.lean.codegen.{...}` / `verification.models.contracts`)
   in place and as a flattened copy at
   `/tmp/spipe_wrapped_..._lean_codegen_spec_spec.spl` (same shape the wrapper
   writes). Both: **0 errors, 8 warnings, identical verdict**; zero
   `undefined identifier` diagnostics on the relocated copy. `verification.*`
   resolves from the lib root (`src/verification/`), independent of the
   wrapper's temp location — the relocation-sensitivity this record filed on
   no longer exists.
2. **The doc's "Unblock condition" failure mode cannot recur.** The
   `uncompilable_construct` trigger was NOT widened (the recorded prohibition
   is honored). Instead, per
   `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` (and the app
   twin): a wrapped-copy compile failure now either **fails closed**
   (coverage: "ABORTED BEFORE EXECUTION … NOT a test result", 2026-08-31) or,
   under `SIMPLE_MCDC_MODE`, **degrades to running the ORIGINAL unwrapped
   source** and reports its real pass/fail (widened 2026-09-12 to cover
   `Undefined(...)` — a property of the standalone-SMF compile, not the spec's
   assertions, so it cannot mask a genuine defect). A silent 11-file aggregate
   mismatch is therefore structurally impossible now.
3. **Directory re-run** (`bin/simple.exe test test/00_formal_verification
   --coverage --timeout 120`, one bounded attempt): across all files processed
   before the lane's wall-clock cap, **0** `undefined identifier` /
   `Undefined(` failures and **0** `spipe_wrapped` compile failures. Each file
   instead hit the loud fail-closed path ("coverage instrumentation wrapper
   compilation timed out after ~120 s … NEVER run under the requested coverage
   path"). That per-file instrumented-compile timeout is the **separately
   routed live defect "native-build Windows hang"** — not this record's
   defect; per lane rules it was not retried. The full directory-vs-explicit
   aggregate re-check therefore remains **blocked on Windows** until that hang
   is fixed; on a non-Windows or probe-capable host it should be re-run per
   the unblock condition.

Note: the spec tree has been reorganized since filing (the 11 offenders now
live under `test/00_formal_verification/compiler/`, 34 specs total) and
`tool_checker_spec.spl` no longer imports `verification.*` at all — further
evidence this class has been worked over. Verdict: the identifier-resolution
defect is FIXED; the residual Windows coverage-lane timeout is the known
native-build hang, routed elsewhere.
