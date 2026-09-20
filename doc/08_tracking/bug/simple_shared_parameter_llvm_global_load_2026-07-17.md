# `shared` Parameter Lowers As Undeclared LLVM Global
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Symptom

During a full pure-Simple bootstrap, Stage 2 native-build failed for the HIP
and OpenCL backend contract modules with:

`llvm global load referenced undeclared symbol Shared`

Both failures used `shared` as a local and parameter name, then read fields
from that parameter. Renaming the binding to `contract` allows compilation to
proceed without changing behavior.

## Expected

Lowercase local and parameter bindings named `shared` must remain local SSA
values during LLVM lowering. They must not be canonicalized into a global or
variant symbol named `Shared`.

## Reproduction

Run the full bootstrap native-build over a module containing a typed parameter
named `shared` followed by a field read such as `shared.source`.

## Follow-up

Add a focused LLVM-lowering regression and fix name classification so local
bindings take precedence over global/variant canonicalization.

