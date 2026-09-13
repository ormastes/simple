# Stage4 post-HIR corrupt module runaway

**Status:** OPEN (unverified 2026-09-12)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
