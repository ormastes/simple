# Explicit parser Error was erased to inference

Issue: https://github.com/ormastes/simple/issues/3032

Status: source repair and focused regression authored; execution pending.

At C36 manual source `aeb2517fac0a3f287aed4347d75235ac8976161d`,
`HirLowering.lower_type` sends `TypeKind.Error` through its final fallback to
`HirTypeKind.Infer(0,0)` without recording a diagnostic. This is a source-proven
error-erasure defect, independently of unresolved imported-owner failures.

The exact-discriminant Error branch now uses the existing `self.error` contract
and returns `HirTypeKind.Error` with the original span. That API appends both a
LoweringError and the driver's parallel diagnostic message/recovered streams,
marking the error unrecovered. Existing invalid Named extraction already uses
this same path. Recursive composite lowering therefore retains the invalid
payload and a fatal diagnostic rather than accepting inference.

No public signatures change. Legitimate Infer, Atomic and other discriminants
retain their existing handling. In particular this does not implement missing
Atomic lowering or claim it preserves a capability across all phases.

## Adapter rejection contract

The separately owned #3021 monomorphization adapter has no actual parser Handle
variant. A proposed unsupported Handle conversion can yield parser Error only
when consumers reject that error. This change makes the HIR path explicit.
The reverse adapter's fixed `ConcreteType` return signature requires its own
explicit rejection of Error; merely replacing Error with Named("Unknown") is
not acceptable. No invented nominal Handle or pointer reinterpretation is
introduced here. Adapter changes remain separate and require review.

## Verification boundary

The real lower_type spec checks direct Error result/span/unrecovered diagnostic,
nested array/Optional Error, legitimate Infer, and non-Error named/Atomic
discriminants. It does not test by source-string inspection or fake diagnostics.
No native build or SSpec execution was performed. Source review and coordinated
manual affected-file checks remain required; this is not whole-CLI admission.
