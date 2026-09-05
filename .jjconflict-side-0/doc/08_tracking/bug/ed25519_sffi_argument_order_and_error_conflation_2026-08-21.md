# Ed25519 SFFI argument order and error conflation

Date: 2026-08-21

Status: PARTIALLY FIXED — `/root`, SFFI v2 hardening lane

Severity: critical (valid signatures rejected in native lane; malformed bridge
inputs indistinguishable from cryptographically invalid signatures)

## Finding

The interpreter and every Simple declaration pass
`(message, public_key, signature)`, while the Rust native export previously
interpreted the first two arguments as `(public_key, message)`. The legacy ABI
also returned zero for malformed runtime values, invalid key/signature lengths,
and an authentic cryptographic rejection.

## Fix

- align the Rust native export with the established Simple/interpreter order;
- add `rt_ed25519_verify_checked`, returning `1` for valid, `0` for a validly
  formed but rejected signature, and `-1` for malformed bridge input;
- expose `ed25519_verify_native_checked -> Result<bool, text>`;
- cover the native order with an existing deterministic Ed25519 fixture.

## Remaining migration

Security-sensitive callers should move to the checked wrapper or the in-tree
pure-Simple Ed25519 verifier. RSA and ECDSA native wrappers need the same typed
error treatment before the entire signature SFFI family can be marked hardened.
