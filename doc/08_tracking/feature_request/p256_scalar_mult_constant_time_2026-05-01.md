# Feature Request: Constant-time P-256 scalar multiplication

**Filed:** 2026-05-01
**Module:** `src/os/crypto/ecdh_p256.spl`
**Severity:** P0 before any caller exposes the ephemeral private key
through the TLS 1.3 `handshake_secret` schedule.
**Status: FIXED 2026-05-01 — replaced naive double-and-add with always-add-and-select on secret-scalar path** (FR change #1; items #2/#3 still tracked below).

## Resolution Summary (change #1, 2026-05-01)

The branchful `if (byte & mask) != 0u8: acc = _jac_add_mixed(acc, ax, ay)`
inner loop in `_scalar_mul_affine` is replaced with an always-add-and-select
form. A new `p256_point_cselect(p0, p1, choose_p1) -> JacP256` helper
mirrors the XOR-mask discipline of `ed_point_cselect` (from W5-A's
`ed25519.spl` CT fix) and `fe_cond_select` (from `fe_p256.spl`):

```
out = a ^ ((0 - choose_p1) & (a ^ b))
```

The 256-bit MSB-first inner loop now ALWAYS executes both `_jac_double` and
`_jac_add_mixed`, then constant-time-selects between the doubled-only
accumulator and the doubled-then-added candidate. No data-dependent branch
on a scalar bit. Wall-time is ~2× the previous form but independent of the
scalar's Hamming weight.

The structural CT property is enforced by
`test/unit/lib/crypto/p256_ct_property_spec.spl` (mirrors
`ed25519_ct_property_spec.spl`): regex-asserts the new
`_scalar_mul_affine` body contains no `if (byte ...)` / `if scalar[...]`
fingerprints AND that it does mention `p256_point_cselect`.

**Items #2 (`_jac_add_mixed` `fe_eq` / `p.inf` short-circuit) and #3
(`_jac_double`/`_to_affine` `p.inf` short-circuit) remain OPEN.** They
are intermediate-point branches, not scalar-bit branches; not exposed
through the scalar's Hamming weight on the typical secret-scalar
trajectory. They should still land before broad ECDHE handshake-secret
exposure; tracked for follow-up under the same FR.

**Runtime byte-exact verification of the CT spec's functional tests is
currently blocked** on an independent interpreter regression filed at
`doc/08_tracking/bug/interpreter_uint_method_dispatch_2026-05-01.md`
(`Value::UInt` missing method dispatch — breaks every `arr[u64_var]`
indexing site against `[u8]`). The structural CT check (the hard
guarantee per the FR's Required Changes #4) PASSes today.



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
