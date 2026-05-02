# Traceability Progress Report

Date: 2026-03-28

## Summary

Traceability implementation in `src/app/traceability/` is now functionally in place for the covered rules. The focused unit spec passes against the current local Simple binaries, and the source tree contains the CLI entrypoint, dispatch branch, and help text for `simple traceability-check`.

The remaining gap observed in this checkout is not traceability rule logic. It is release artifact drift: the checked-in `bin/release/linux-x86_64/simple` binary is older than the current source tree and does not yet expose `traceability-check`, even though the command is wired in source.

## Implemented

- Added traceability helper exports in [src/app/traceability/__init__.spl](/Users/ormastes/simple/src/app/traceability/__init__.spl).
- Added manifest/default-root helper functions in [src/app/traceability/core.spl](/Users/ormastes/simple/src/app/traceability/core.spl).
- Updated the focused spec in [test/unit/app/tooling/traceability_spec.spl](/Users/ormastes/simple/test/unit/app/tooling/traceability_spec.spl) to use manifest-style inputs instead of direct virtual-file arrays.
- Verified the focused spec passes with the current local binary:
  - `src/compiler_rust/target/bootstrap/simple test test/unit/app/tooling/traceability_spec.spl`
- Verified the source tree wires the CLI command through:
  - [src/app/traceability/main.spl](/Users/ormastes/simple/src/app/traceability/main.spl)
  - [src/app/cli/main.spl](/Users/ormastes/simple/src/app/cli/main.spl)
  - [src/app/cli/dispatch/table.spl](/Users/ormastes/simple/src/app/cli/dispatch/table.spl)
  - [src/app/cli/cli_helpers.spl](/Users/ormastes/simple/src/app/cli/cli_helpers.spl)
- Added CLI-facing regression coverage for `traceability-check` in [test/unit/app/cli/traceability_command_spec.spl](/Users/ormastes/simple/test/unit/app/cli/traceability_command_spec.spl) and updated the static CLI inventory/help specs to include the command.
- Source mapping helpers are present for:
  - source file to unit spec candidates
  - source directory to integration/module spec candidates
- Text parsing helpers are present for:
  - relative path extraction
  - `REQ-*` and `NFR-*` identifier extraction
  - date-suffixed slug normalization

## Current Verification

Passing focused command:

```text
src/compiler_rust/target/bootstrap/simple test test/unit/app/tooling/traceability_spec.spl
```

Observed result:

- `Passed: 10`
- `Failed: 0`

Stale release artifact behavior:

- `bin/release/linux-x86_64/simple traceability-check ...`
- Result: `error: file not found: traceability-check`

Attempted rebuild status:

- `src/compiler_rust/target/bootstrap/simple native-build --entry src/app/cli/main.spl -o build/traceability_cli_check`
- Result: no output binary emitted because the native build hit an unrelated parse failure in `src/lib/nogc_sync_mut/web_ui/dom_backend.spl`
- Reported failure: `parse: Unexpected token: expected identifier, found Assign`

This indicates the release binary in the checkout has not been rebuilt from the current CLI source, and the current blocker is outside the traceability module.

## What Was Learned

- The earlier report state is outdated relative to the current checkout.
- The manifest helper path is stable enough for the focused traceability spec to pass.
- The main user-visible risk is stale binary packaging, not missing analysis/counting logic.
- CLI regression coverage needs to include new commands explicitly; otherwise source wiring can exist without any guard at the user-facing layer.

## Next Work

- Fix the unrelated native-build parse failure in `src/lib/nogc_sync_mut/web_ui/dom_backend.spl`, then rebuild the release binary so `bin/release/linux-x86_64/simple` reflects the current CLI command set.
- Add or keep CLI-level regression checks for `traceability-check` so command registration/help drift is caught immediately.
- After rebuilding, validate `simple traceability-check --scope=all` through the release binary, not just through source-level dispatch/tests.

## Version Control

Previous pushed progress commit:

- `7403c2f2` — `test: adapt traceability spec to manifest helpers`
