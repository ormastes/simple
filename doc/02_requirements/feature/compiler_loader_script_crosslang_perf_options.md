<!-- codex-research -->
# Compiler loader script cross-language performance: feature options

No option is selected. The user must explicitly choose one; then this options
file is deleted and the chosen requirements are written to the final feature
requirements document.

## Option A — Complete the focused semantic and evidence contract

Require all current provisional REQ-001..REQ-008 behavior: fail-closed
self-hosted admission; equivalent cross-language checksums; bounded retained
reports; caller-correct negative caching; exact reset behavior; packed-byte
collection parity; and scoped, descriptor-bounded, non-escaping foreign byte
capabilities. Stage 2/3 bootstrap evidence remains diagnostic and cannot be
substituted for a deployed CLI row.

- Pros: matches the executable spec and current implementation boundaries;
  closes every known PBL/LDR/PRV/BYT/XLG gap without expanding product scope.
- Cons: completion remains blocked wherever an admitted deployed CLI is
  mandatory; spans compiler, runtime, SFFI, tests, and scripts.
- Effort: L, approximately 12-20 files including tests and documents.

## Option B — Semantic completion with deferred live performance rows

Require loader correctness, packed-byte behavior, foreign capability safety,
source-contract validation, and Stage 2/3 bootstrap diagnostics now. Retain
live self-hosted latency/RSS/cross-language rows as explicit follow-up
requirements rather than acceptance for this delivery.

- Pros: permits a meaningful safety/correctness completion while the deployed
  CLI is independently blocked; keeps every unavailable row visible.
- Cons: does not deliver the headline end-to-end performance evidence; requires
  a follow-up selection and acceptance cycle.
- Effort: M, approximately 8-14 files plus a tracked follow-up.

## Option C — Loader/probe-only delivery

Limit this feature to negative-cache correctness and failed-existence-probe
instrumentation. Move packed-byte and cross-language performance concerns into
separate named features with independent requirements and plans.

- Pros: smallest ownership surface and clearest loader-specific acceptance;
  easier independent review.
- Cons: splits the already-integrated spec/manual and delays byte/SFFI and
  harness completion; requires careful traceability migration.
- Effort: M, approximately 6-10 files here plus two new feature-document sets.
