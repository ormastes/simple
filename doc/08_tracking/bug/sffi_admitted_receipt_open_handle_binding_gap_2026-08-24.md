# SFFI admitted receipt is not yet bound to the open provider handle

**Status:** open  
**Severity:** P0 for safe/critical dynamic-provider admission

## Evidence

`simple.sffi-admission.v1` binds signed evidence to an exact artifact SHA-256,
ABI registry, provider, target, signer, report, and symbol signatures. The
canonical Simple parser validates those fields before cached integer slots are
published. However, `VersionedDynLib` still obtains the library through a
pathname `dlopen`-style operation and carries no loader-minted identity proving
that its already-open object is the artifact named by the receipt.

Ordinary Simple code can also construct `SffiAdmissionReceiptV1`; parsing a
receipt is validation, not signature authority. For that reason
`resolve_evidence_bound_i64_manifest` remains explicitly
`unsafe(ffi, raw_ptr)` and must not be advertised as a safe or verified API.

## Required closure

The platform loader must open an immutable artifact handle, hash and verify the
same object, resolve its complete ABI closure, and mint a package-private token
bound to the provider generation. Cached thunks may be published only from that
token. Hashing, signature verification, pathname work, and symbol lookup remain
one-time admission work; the hot call stays a cached typed dispatch plus its
status/null checks.

## Current verification boundary

The shell evidence sabotage contract passed once before the subsequent
2 MiB/8,192-symbol allocation caps and their fixtures were added. There is no
admitted current-source Stage-4 executable in this worktree, so the new Simple
parser spec and OptimizerPlugin pass have not run. Those deltas remain
`UNVERIFIED`; the Rust-seed/shared binary must not be substituted as proof.
