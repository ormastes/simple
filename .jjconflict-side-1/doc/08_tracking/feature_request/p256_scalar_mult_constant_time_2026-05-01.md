# Feature Request: Constant-time P-256 scalar multiplication

**Filed:** 2026-05-01
**Module:** `src/os/crypto/ecdh_p256.spl`
**Severity:** P0 before any caller exposes the ephemeral private key
through the TLS 1.3 `handshake_secret` schedule.
**Status:** OPEN

## Context

The P-256 NamedGroup advertise + ephemeral keypair gen landed for TLS 1.3
on 2026-05-01 (see `crypto_recovery_status.md` Wave 1 outcomes). The
scalar-multiplication routine `_scalar_mul_affine` in `ecdh_p256.spl`
uses Jacobian coordinates with affine-mixed point addition over the
constant-time `fe_p256.spl` field primitives, but the EC layer itself is
**NOT** constant-time:

* `_jac_add_mixed` short-circuits via `if p.inf:` and via the equal-points
  branch `if fe_eq(p.x, u2): if fe_eq(p.y, s2): return _jac_double(p)`.
  Both branches are timing- and cache-observable when the secret scalar
  drives intermediate points to the curve's identity / doubling cases.
* `_to_affine` short-circuits on `if p.inf:` returning `(zero, zero)`.
* The 256-bit MSB-first scalar loop in `_scalar_mul_affine` performs an
  add only when the bit is `1` (`if (byte & mask) != 0u8`) — classic
  square-and-multiply timing leak.

This is acceptable today **only** because the M3 advertise-only landing
does not yet feed the ephemeral private scalar into `handshake_secret`
derivation; the wire only carries the public key. Once the deferred
ECDHE shared-secret + key_schedule integration lands (HRR connect-flow
pickup point), this becomes a real side-channel hole.

## Required Changes

1. Replace the conditional add in `_scalar_mul_affine` with a
   constant-time conditional point select (analogous to
   `fe_cond_select` in `fe_p256.spl`), so add+double fire on every bit.
2. Replace the equal-points / point-at-infinity branches in
   `_jac_add_mixed` with a complete-addition formula that handles all
   exceptional cases without branching (e.g. Renes-Costello-Batina
   2016, "Complete addition formulas for prime order elliptic curves").
3. Remove the `if p.inf:` branch in `_jac_double` and `_to_affine`;
   represent point-at-infinity via a masked Z-coordinate so the same
   formulae apply.
4. Add a CT property spec analogous to
   `test/unit/lib/crypto/ed25519_scalar_mul_ct_spec.spl` checking that
   the same instruction trace fires for low-Hamming-weight and
   high-Hamming-weight scalars.

## Blockers Cleared When This Lands

* TLS 1.3 ECDHE handshake_secret derivation through `p256_ecdh_shared_x`.
* HRR connect-flow integration (which will route a P-256 ephemeral
  through the live handshake state machine).

## References

* RFC 8446 §6 + §7 — handshake-secret derivation requires the ECDHE
  scalar to remain secret.
* SafeCurves "Why P-256 is hard to implement constantly":
  https://safecurves.cr.yp.to/timings.html
* BoringSSL `crypto/fipsmodule/ec/p256.c` for the reference CT
  implementation pattern.
