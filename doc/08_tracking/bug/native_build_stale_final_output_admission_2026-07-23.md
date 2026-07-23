# native-build stale final output admission

**Status:** Fixed in source; focused qualification pending.

## Problem

`native-build` previously accepted `CompileResult.Success` when the requested
output path already existed, even if the driver/linker did not write a new
artifact. This could report success for and retain an older binary.

## Fix

The shared pure-Simple CLI funnel now writes to a process-unique owned sibling
staging path, requires that fresh artifact to exist, and uses the native rename
facade to replace the requested output only after success. Compile
or link failure preserves the previous requested output and removes partial
staging output. Metadata publication is a later, separate required step; a
metadata write failure can report failure after the fresh binary was published.

## Regression evidence

`test/01_unit/app/cli_native_build_main_contract_spec.spl` checks the staging,
fresh-artifact admission, and publish path. Its new staging scenario passes
through the temporary bootstrap interpreter; the enclosing legacy contract
still has two unrelated failures, so behavioral native-build qualification is
pending.
