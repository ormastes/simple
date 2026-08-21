# SFFI v2 P0 fail-closed behavior

> Authored manual, not generated. The isolated documentation worktree did not
> contain a runnable deployed pure-Simple `bin/simple`, so `spipe-docgen` could
> not produce an admitted generated manual on 2026-08-21. The executable source
> of truth is `test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl`.

This focused system specification runs independent Simple programs in fresh
subprocesses. It observes exit status and public output/diagnostics only; it
does not inspect compiler source text as behavioral evidence.

## REQ-SFFI-V2-001/002: declared return contracts distinguish and reject missing values

### Missing non-optional return

1. Run a non-optional `text` function whose body falls through.
2. Confirm execution fails instead of fabricating `nil`.
3. Confirm the diagnostic contains `E-SFFI-016`.

Probe: `sffi_v2_missing_nonoptional_return_probe.spl`.

### Unit fallthrough control

1. Run a unit-returning function whose body falls through.
2. Confirm the process succeeds.
3. Confirm stdout contains `UNIT_OK`.

Probe: `sffi_v2_unit_fallthrough_probe.spl`.

### Explicit optional absence control

1. Run an optional `text` function that explicitly returns `nil`.
2. Confirm the process succeeds.
3. Confirm stdout contains `NONE_OK`.

Probe: `sffi_v2_explicit_optional_nil_probe.spl`.

## REQ-SFFI-V2-005/006: unresolved externs fail without fabricated values

### Missing symbol admission

1. Invoke a deliberately nonexistent extern symbol.
2. Confirm the process fails.
3. Confirm the diagnostic contains `E-SFFI-001` and the unresolved symbol name.

### No fabricated result

1. Reuse the result from the missing-symbol admission probe.
2. Confirm the process failed.
3. Confirm stdout is empty, proving execution did not continue by printing a
   fabricated integer zero.

Probe: `sffi_v2_unresolved_dynamic_extern_probe.spl`.

## Current probe status

Direct bootstrap-only probing (not release evidence) showed:

- unit fallthrough: succeeded with `UNIT_OK`;
- explicit optional `nil`: succeeded with `NONE_OK`;
- missing non-optional return: incorrectly succeeded and printed `nil`;
- unresolved extern: failed and named the symbol, but did not yet contain
  `E-SFFI-001`.

The last two results demonstrate that the executable spec is red before the P0
implementation. They are not claimed as accepted pure-Simple SPipe evidence.
