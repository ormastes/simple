# Stage-3 imported composite prebind skips dependencies (2026-08-21)

## Status

The idempotence hardening is implemented, but final bootstrap verification
failed. This was not the root cause of the staged unresolved-type cascade.

## Evidence

A receipt-bound Stage 3 completed all 954 streaming surfaces and advanced into
HIR, but reported `Span` and `OptimizationLevel` from `driver.spl`, which names
neither type. The same payload repeated through unrelated package siblings.
The earlier owner-by-name route fix was active, so canonical import routes were
available.

## Root cause

Package/facade registration may prebind an imported composite. The composite
branch then returned before walking its public fields. Field types such as
`Span` were therefore projected without materializing the defining module's
explicit dependency route. An Optional symbol lookup also made the branch
unsafe under staged native projection.

## Hardening and regression

Use scalar `lookup_or_invalid`; define only when absent, but always execute the
idempotent field dependency closure and imported-method registration. A
bootstrap source contract prevents restoring the early return.

## Verification result

The third receipt-bound run again emitted the original first diagnostics in
`driver.spl`: nine unresolved `Span` dependencies surrounding one unresolved
`OptimizationLevel`, followed by `ProcessResult` in `file_ops.spl`. The run was
stopped after this exact recurrence under the three-cycle verification cap.
Stage 3/4 and the bootstrap must-check therefore remain blocked; no push is
permitted.
