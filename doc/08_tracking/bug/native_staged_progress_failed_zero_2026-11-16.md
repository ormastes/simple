# native_staged progress reports `failed=0` while batches are withheld

- **Status:** fix proposed (this change); spec NOT_RUN (no runnable full-CLI binary on this host)
- **Found:** 2026-11-16, bootstrap cycle 9 (`/tmp/orchestrator-cycle7-bootstrap-bridge-20261116/prototype-cycle9/build.log`)
- **Producer:** stage2-admitted `simple`, sha256 `bc9d676a0bb185378b72035f99de892c5af3b0169e6207559f9e385d3a4cb106`
- **Owner code:** `src/compiler/80.driver/driver_aot_pipeline.spl` (`native_staged_codegen_flush_v1`),
  `src/compiler/80.driver/driver_build/native_staged_codegen.spl`

## Observed

At one point in the same log:

```
[build] phase=mir           ... done=704 total=1622 succeeded=594 failed=110 ...
[build] phase=native_staged ... done=208 total=1622 succeeded=208 failed=0  ...
```

plus 112 `[ERROR] [mir-module-failure]` lines. The `mir` line counts failures
correctly (`mir_failed_modules`). The `native_staged` line passes a literal `0`
as `failed` (`driver_aot_pipeline.spl:657-661`; the producer-era copy at
`8a787ae130a:…:644-648` is identical). That literal is the bug.

## Why it matters

Outside go-to-end mode a batch that holds one failed module is flushed with
`lowering_failed=true`. Its verify, borrow and codegen gates are skipped, so
none of its modules emits an object, all 8 including the 7 good ones. Nothing
prints for it either: the `[staged-codegen] batch N failed` line fires only for
`batch_failed`, which counts `ctx` errors, and MIR lowering errors only reach
`ctx` in the final collector. In cycle 9, 496 lowered modules had been silently
withheld while the progress line read `failed=0`.

**What was not affected:** the build verdict. At the end,
`_driver_collect_mir_errors` adds every fatal MIR error to `ctx`, and
`lower_to_mir` returns false, so this lane does not link a binary with rt_panic
placeholders and exit 0. The defect is the progress counter and the silent
withholding of good objects, not a fail-open link. Under go-to-end, failed
modules are kept out of the batch, so the other modules still emit.

## Fix

- `NativeStagedCodegenStateV1.modules_withheld` counts the modules of each
  flushed batch that did not reach an object. The count is the batch size minus
  how far `modules_flushed` advanced for that batch
  (`native_staged_withheld_count_v1`, a pure function).
- The progress line passes `modules_withheld` as `failed`. Non-mir phases keep
  their contract that failures are not included in `done`.
- A batch withheld by a lowering or verify gate now prints
  `[staged-codegen] batch N withheld K module(s) …`.

## Verification

- Spec: `test/01_unit/compiler/driver/native_staged_codegen_spec.spl`, describe
  "the native_staged progress failure count" (4 cases).
- **NOT_RUN.** This host has no deployed `bin/simple`, and the only admitted
  binary (bc9d) is the bootstrap CLI, which supports only `compile` and
  `native-build`. The red state is shown statically: before this change the
  `failed` argument is the literal `0`, and the symbols the spec imports do not
  exist. Run the spec green on the next qualified full CLI.

## Follow-up (not in this change)

A withheld batch throws away the objects of its good modules, so the next cycle
recompiles them. Passing only the good modules to codegen, as go-to-end already
does, would let the cache keep them. That is a behaviour change to admission
and needs its own review.
