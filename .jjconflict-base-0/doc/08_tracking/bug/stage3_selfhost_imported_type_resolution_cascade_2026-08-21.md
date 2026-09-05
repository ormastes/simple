# Stage-3 self-host imported-type resolution cascade (2026-08-21)

## Status

Fix committed locally; bootstrap re-verification pending in a fresh session.
Measured Stage 2 passes compilation, sanity, receiver
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

This is not the earlier missing sibling-impl link defect. Phase 2 intentionally
clears `ctx.modules` after freezing streaming module surfaces, but production
Phase 3 selected its cached-module path from an adjacent mutable readiness flag
that native value semantics did not retain. It then read the empty module map;
package sibling surfaces amplified the result into package-uniform diagnostics.

## Unblock condition

The fix routes from stable streaming configuration, recovers the frozen owner,
uses positive dictionary membership, and fails closed if a non-streaming path
ever sees sources with an empty parser cache. A lifecycle regression exercises
the production dispatcher with the readiness flag deliberately reset. Rerun
Stage 3 once in a fresh bounded verification session; do not patch 197
consumers individually or accept a seed fallback.
