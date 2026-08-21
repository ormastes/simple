# Stage-3 imported composite prebind skips dependencies (2026-08-21)

## Status

Pure-Simple fix implemented; final bootstrap verification pending.

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

## Fix and regression

Use scalar `lookup_or_invalid`; define only when absent, but always execute the
idempotent field dependency closure and imported-method registration. A
bootstrap source contract prevents restoring the early return. The final gate
is a fresh receipt-bound Stage 3/4 convergence run.
