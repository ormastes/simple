# TLS CertificateVerify repeated raw foreign verification

**Status:** fixed in the current SFFI hardening worktree

## Defect

The TLS 1.3 client Ed25519 CertificateVerify path invoked two raw verification
symbols for debug output and then invoked a third provider path for the actual
decision. One of those decision symbols,
`rt_tls13_cert_verify_ed25519`, had no owned Simple declaration. The other two
were duplicate untagged declarations in `_Tls13/context_io.spl` even though the
module already imported the canonical signature SFFI owner.

This was both an unsafe-boundary defect and unnecessary public-key work on the
handshake path. A zero/nil result from the ambient symbol could be confused
with a provider result, while valid Ed25519 handshakes paid for three
verification operations.

## Fix

Both transport modes now call
`verify_certificate_verify_msg_scheme` exactly once. That function routes the
Ed25519 case through `ed25519_verify_native_checked`, whose raw call is confined
to the canonical minimal `unsafe(ffi)` helper and whose negative bridge status
becomes a typed error. The duplicate declarations and raw debug calls were
removed.

The change introduces no lookup, hash, allocation, copy, or wrapper dispatch
beyond the already-selected canonical verifier. Algorithmically, the Ed25519
CertificateVerify boundary drops from three public-key verification operations
to one.

## Evidence

- The raw-SFFI declaration ratchet decreased from 12,799 to 12,797 identities
  and passed after the reviewed baseline reduction.
- The optimizer completed at O3 for `context_io.spl` and `handshake.spl`; it
  reported only broad pre-existing opportunities.
- The focused Ed25519 CertificateVerify vector suite completed under the Rust
  bootstrap seed. This is compatibility evidence, not authoritative Stage-4
  verification.
- The broader X25519MLKEM768 source-contract suite still has two unrelated
  pre-existing failures in its X25519 diagnostic and entropy-runtime checks;
  the new single-verifier assertions did not fail.

Production provider signing/admission remains separate and incomplete.
