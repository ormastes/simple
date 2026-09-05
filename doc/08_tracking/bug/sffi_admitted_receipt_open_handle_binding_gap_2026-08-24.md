# SFFI admitted receipt is not yet bound to the open provider handle

**Status:** open  
**Severity:** P0 for safe/critical dynamic-provider admission

## Evidence

`simple.sffi-admission.v1` binds signed evidence to an exact artifact SHA-256,
ABI registry, provider, target, signer, report, and symbol signatures. The
canonical Simple parser validates those fields before cached integer slots are
published. Linux now loads a sealed snapshot rather than reopening mutable
pathname bytes. Receipt and exact-artifact carrier fields are now file-private,
so HIR lowering rejects aggregate construction outside their canonical owner
modules. Public accessors expose identity only; exact-handle resolution remains
explicitly unsafe.

Ordinary application code can parse and inspect a receipt but cannot directly
construct its private fields. Parsing caller-supplied text is still validation,
not signature authority. For that reason
`resolve_evidence_bound_i64_manifest` remains explicitly
`unsafe(ffi, raw_ptr)` and must not be advertised as a safe or verified API.

Linux pathname and in-place mutation are closed by copying into a memfd and
applying `F_SEAL_WRITE`, `F_SEAL_GROW`, `F_SEAL_SHRINK`, and `F_SEAL_SEAL`
before hashing or loading. Production-C sabotage proves write rejection and
replacement resistance; the Rust counterpart proves byte preservation and all
four seals. The public loader still accepts a caller-supplied expected digest,
so the carrier is not yet a loader-minted cryptographic authority.

## Required closure

The file-private carrier half is implemented. The compiler/runtime must still
mint an unforgeable token bound to provider generation from an actual
signature/trust-policy verification result. Cached thunks may be published
only from that token. Other
platforms need equivalent immutable-snapshot semantics or fail-closed critical
rejection. Hashing, signature verification, copying, and symbol lookup remain
one-time admission work; the hot call stays a cached typed dispatch plus its
status/null checks.

## Current verification boundary

The shell evidence sabotage contract passed once before the subsequent
2 MiB/8,192-symbol allocation caps and their fixtures were added. There is no
admitted current-source Stage-4 executable in this worktree, so the new Simple
parser spec, visibility spec, and OptimizerPlugin pass have not run. Those
deltas remain `UNVERIFIED`; the Rust-seed/shared binary must not be substituted
as proof.

The Linux sealed-snapshot primitive itself has stronger evidence: strict C
syntax checks pass for both runtime owners; the production-C replacement/write
sabotage passes; the Rust interpreter and native-runtime focused tests each
pass 1/1; and Cargo checks both runtime and compiler registrations. This does
not discharge the separate Simple source-forgeability or Stage-4 optimizer
obligations.

The file-private carrier slice was exercised once through the available
bootstrap seed: the focused SFFI admission spec passed 7/7 in 6.03 s with
175,472 KiB peak RSS, including identity rejection before foreign-handle use.
This is compatibility evidence only because that executable identifies itself
as a Rust bootstrap seed. The broader HIR visibility spec remains blocked by
the already-recorded missing `rt_heap_ref_wellformed` seed extern (17/17
examples failed; 20.14 s, 410,292 KiB), so current-source visibility execution
is still unverified. Optimizer O3 analysis completed once for the three touched
production Simple files (4.48--4.96 s, 288,308--290,928 KiB); it reported only
the scanner's broad existing opportunity sets. Runtime call bodies did not
change, so no per-call benchmark was repeated.
