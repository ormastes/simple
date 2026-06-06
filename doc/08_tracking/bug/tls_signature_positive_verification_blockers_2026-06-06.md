# TLS Signature Positive Verification Blockers

**Filed:** 2026-06-06
**Status:** Open
**Area:** `src/os/tls13/`, `std.nogc_sync_mut.io.signature_sffi`, OS crypto system specs

## Summary

The TLS/server signature path now fails closed instead of emitting a malformed
CertificateVerify with an empty signature, but positive signature verification
is not production-ready on this worktree.

Current evidence:

- `bin/simple test test/03_system/os/os_rt_ed25519_sign_spec.spl --clean --json`
  - `total_passed: 5`, `total_failed: 3`
  - PKCS#8 Ed25519 signing returns 64-byte deterministic signatures, but
    `ed25519_verify` and `openssl pkeyutl -verify` reject the produced
    signatures.
- `bin/simple test test/03_system/os/os_rt_rsa_pss_verify_spec.spl --clean --json`
  - `total_passed: 9`, `total_failed: 3`
  - Tampered/wrong-input rejection works, but known-good RSA-PSS SHA-256,
    SHA-384, and SHA-512 positive fixtures are rejected.
- `bin/simple test test/03_system/os/os_tls_cert_chain_spec.spl --clean --json`
  - `total_passed: 1`, `total_failed: 3`
  - Leaf pieces parse, but RSA-PSS signature verification rejects the leaf and
    `verify_cert_chain` reports `unsupported certificate signature algorithm`
    on the valid chain.
- `bin/simple test test/01_unit/os/tls13/server_accept_spec.spl --clean --json`
  - `total_passed: 32`, `total_failed: 0`
  - Server CertificateVerify generation returns `[]` when signing fails, and
    handshake preparation stops with `certificate_verify_failed` instead of
    emitting an empty-signature server flight.
- `bin/simple test test/01_unit/os/tls13/cert_verify_ed25519_spec.spl --clean --json`
  - `total_passed: 6`, `total_failed: 0`
  - Pure Simple Ed25519 now accepts valid CertificateVerify signatures and
    rejects wrong-key/tampered signatures. TLS no longer falls through to the
    permissive runtime fallback after pure Simple rejection.

## Required Fix

Restore positive SFFI signature verification/signing interop for Ed25519 and
RSA-PSS, then tighten `server_accept_spec.spl` back to require a real
CertificateVerify and encrypted server flight for the valid fixture path.
