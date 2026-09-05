# Stage4 post-HIR corrupt module runaway

## Reproduction

After facade extraction progressed, Stage4 printed `functions=-1`, retained the
module, and stayed at 99.9% CPU while RSS grew to 16,562,144 KiB at 20:20
elapsed. A fail-fast probe then reproduced the same `-1` for `app.cli.main`.

## Cause and fix

The aggregate was not corrupt. Native bootstrap `Dict.len()` is documented to
return `-1`; the HIR lowering code already uses `functions.keys().len()` for
this reason, but the driver called `hir_module.functions.len()` directly. The
driver now counts a typed key array instead. The independently valid fatal HIR
diagnostic exit remains before retention, preserving original errors.

## Regression evidence

`hir_function_count_spec.spl` covers empty, populated, and replacement cases
through the native-safe typed-key helper. The driver source orders the fatal
error exit before shared-trait and phase-module retention.
