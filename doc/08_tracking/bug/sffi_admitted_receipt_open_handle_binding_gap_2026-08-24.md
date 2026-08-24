# SFFI admitted receipt is not yet bound to the open provider handle

**Status:** open  
**Severity:** P0 for safe/critical dynamic-provider admission

## Evidence

`simple.sffi-admission.v1` binds signed evidence to an exact artifact SHA-256,
ABI registry, provider, target, signer, report, and symbol signatures. The
canonical Simple parser validates those fields before cached integer slots are
published. Linux now loads a sealed snapshot rather than reopening mutable
pathname bytes. The remaining authority carrier is not loader-private, so
ordinary source can still construct values resembling an admitted token.

Ordinary Simple code can also construct `SffiAdmissionReceiptV1`; parsing a
receipt is validation, not signature authority. For that reason
`resolve_evidence_bound_i64_manifest` remains explicitly
`unsafe(ffi, raw_ptr)` and must not be advertised as a safe or verified API.

Linux pathname and in-place mutation are closed by copying into a memfd and
applying `F_SEAL_WRITE`, `F_SEAL_GROW`, `F_SEAL_SHRINK`, and `F_SEAL_SEAL`
before hashing or loading. Production-C sabotage proves write rejection and
replacement resistance; the Rust counterpart proves byte preservation and all
four seals. The carrier type remains constructible by ordinary Simple code.

## Required closure

The compiler/runtime must make the successful snapshot result and signed
receipt package-private and mint an unforgeable token bound to provider
generation. Cached thunks may be published only from that token. Other
platforms need equivalent immutable-snapshot semantics or fail-closed critical
rejection. Hashing, signature verification, copying, and symbol lookup remain
one-time admission work; the hot call stays a cached typed dispatch plus its
status/null checks.

## Current verification boundary

The shell evidence sabotage contract passed once before the subsequent
2 MiB/8,192-symbol allocation caps and their fixtures were added. There is no
admitted current-source Stage-4 executable in this worktree, so the new Simple
parser spec and OptimizerPlugin pass have not run. Those deltas remain
`UNVERIFIED`; the Rust-seed/shared binary must not be substituted as proof.

The Linux sealed-snapshot primitive itself has stronger evidence: strict C
syntax checks pass for both runtime owners; the production-C replacement/write
sabotage passes; the Rust interpreter and native-runtime focused tests each
pass 1/1; and Cargo checks both runtime and compiler registrations. This does
not discharge the separate Simple source-forgeability or Stage-4 optimizer
obligations.
