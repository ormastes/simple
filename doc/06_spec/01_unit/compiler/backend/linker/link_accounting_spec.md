# Linker accounting observation classification

Requirement: ITEM4-REQ-009. Two authored scenarios in
`test/01_unit/compiler/backend/linker/link_accounting_spec.spl`.
Status: **UNRUN**; manually authored companion, not generated execution evidence.

1. Every available observation quality remains MeasuredOnly with certification
   false, for zero, below-limit, equal-limit and above-limit peaks and zero or
   positive caller-supplied limits. Peak and claimed limit remain observable.
2. Negative peaks and unavailable evidence yield NotCertified, zero measured
   peak and certification false, regardless of the claimed limit.

ResourceUsage values here are classifier inputs, never fabricated evidence of
kernel attachment, no-swap, descendant accounting or enforced memory limits.
ExactTree observation alone cannot prove those conditions. The API must not
produce QualifiedJobScope merely because a caller supplied a positive number.

Future execution with an independently admitted self-hosted runtime:
`<runtime> test test/01_unit/compiler/backend/linker/link_accounting_spec.spl`
