# Phase 3 concrete CAS error workaround

Status: source candidate; native verification pending. Not release evidence.

The authenticated Phase 3 build of source 96eaa4da8783f56a3a7954399fbb83573e36afa4
with producer 3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb
lowered 1,142 modules, then failed monomorphization at 35 call sites. Thirty-four
were calls to `cas_batch_error_v1`; the remaining call was `walk_hir_expr`.
Explicit generic arguments were present in the source but discarded before HIR.

This temporary source workaround replaces the generic Err constructor with four
concrete constructors, preserving every error payload and call-site guard:

| Result success type | Call sites |
|---|---:|
| CasBatchTransactionV1 | 7 |
| Unit | 7 |
| text | 18 |
| i64 | 2 |

It does not bypass CAS validation, transaction ownership, fsync, publication,
digest checks, or recovery checks. It does not address `walk_hir_expr`; do not
restart the whole build solely to rediscover that known remaining blocker.

The new native regression exercises six malformed admission inputs and verifies
the exact `incomplete_scc` error before any filesystem access. Existing CAS
publication, corrupt-generation, and corrupt-CURRENT probes remain required.
Neither these new checks nor the existing native probes have run against this
candidate. Structural reverse-transformation is a review aid, not native proof.

Removal gate: apply the explicit-type-argument compiler repair to the producer,
pass the original generic transport and return-context regressions, then revert
the concrete helpers and revalidate CAS probes plus the Phase 3 build. A fetched
fix alone does not satisfy this gate. Related tracking:
`mono_return_context_and_fixed_nominal_binding_2026-10-05`.
