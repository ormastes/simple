# Stage-3 self-host imported-type resolution cascade (2026-08-21)

## Status

Open, release-blocking. Measured Stage 2 passes compilation, sanity, receiver
capability, immutable admission, and receipt-bound replay. Stage 3 fails closed
during HIR lowering before it can emit a provenance-qualified compiler.

## Reproducer

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy \
  --bootstrap-receipt=<planner-admission-v2.env>
```

Evidence:
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

## Observed scope

The 2026-08-21 run produced 410 distinct file/type failures across 197 source
files. The unresolved types are `Backend`, `CodegenBarrierScope`,
`ProcessResult`, `Span`, `TraitBound`, `Type`, and `void`. The first failure is
`ProcessResult` in `src/std/nogc_sync_mut/io/file_ops.spl`; compiler driver,
backend, linker, and VHDL modules then lose shared compiler types.

This is not the earlier missing sibling-impl link defect: Stage 2 links after
explicit owner imports. It is a Stage-3 self-host module/import/re-export type
resolution failure affecting a broad closure.

## Unblock condition

Identify and fix the single import/re-export or module-index invariant that
causes the admitted Stage-2 compiler to lose imported types. Add a focused
multi-module regression that fails on the Stage-2 compiler, then rerun Stage 3
once. Do not patch 197 consumers individually or accept a seed fallback.
