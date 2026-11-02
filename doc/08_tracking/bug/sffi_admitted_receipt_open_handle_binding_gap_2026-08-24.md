# SFFI admitted receipt is not yet bound to the open provider handle
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


Revalidated 2026-11-02: still plausible because no resolution evidence in the body; receipt-to-handle binding is described as still open.

## Analysis 2026-11-02 (lane p0f-2)

Receipt-to-handle binding in current source (`src/lib/nogc_sync_mut/sffi/dynamic.spl`):

- `SignatureVerifiedExactArtifactDynLib.load_signed_linux` verifies the signed
  evidence (`verify_sffi_evidence_v2`, `admission.spl:238`), then calls
  `ExactArtifactDynLib.load_exact_linux(path, admission.artifact_digest())`,
  which hashes the sealed memfd snapshot and rejects a digest mismatch
  (E-SFFI-004) before `dlopen`. The class pairs `sealed` and `admission`
  with file-private fields, so a receipt cannot be re-paired with a different
  handle outside this module, and `resolve_i64_checked` goes only through
  `self.sealed`.
- So the artifact-identity half of the binding already holds on Linux: the
  handle that is opened is the exact byte image the receipt names.

What is genuinely still open (not a bounded change, so no code fix here):

1. `ExactArtifactDynLib.load_exact_linux` and `DynLib.load*` stay public
   (`@unsafe`) and take a caller-supplied digest; there is no loader-minted
   token tying the open handle's `lifetime_identity` to the admitting
   verification result (provider-generation binding).
2. No equivalent immutable-snapshot admission exists off Linux (the
   non-Linux path returns E-SFFI-020; critical rejection is fail-closed
   there, but no safe load exists).
3. A mismatch regression spec cannot be written at the Simple level: the
   carrier fields are file-private (that is the existing defence), and the
   Linux sealed load needs a real provider `.so` and a Linux host, which this
   Windows lane and the Rust seed cannot exercise.

TODO(owner): mint a verifier-owned token (provider generation + artifact
digest) at admission, store it in the `DynLib` registry entry
(`dynlib_lifetime_register_v1`), and have `dynlib_lifetime_begin_v1` reject a
token that does not match; add a Linux-only spec using a sealed test provider.
Status stays open; severity P0 unchanged.
