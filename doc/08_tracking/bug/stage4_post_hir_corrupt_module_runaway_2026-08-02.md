# Stage4 post-HIR corrupt module runaway

## Reproduction

After facade extraction progressed, Stage4 lowered
`src/lib/nogc_async_mut/async/future.spl`, collected four fatal HIR errors, and
then printed `functions=-1`. The driver retained that partial module and stayed
at 99.9% CPU while RSS grew to 16,562,144 KiB at 20:20 elapsed.

## Cause and fix

The non-streaming HIR loop collected diagnostics but did not take the fatal
error exit used by the streaming path. It continued into `phase_hir_modules`
retention and downstream work. The driver now returns immediately after fatal
HIR diagnostics, preserving those original errors, and separately rejects any
negative function-dictionary length before retention.

## Regression evidence

`hir_retention_gate_spec.spl` covers the observed `-1` length plus valid empty
and populated dictionaries. The driver source orders the fatal-error exit
before shared-trait and phase-module retention.
