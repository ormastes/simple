# ECDSA P-256: fresh sign+verify round-trip fails; NIST CAVP vector fails verify

- **Date:** 2026-07-20
- **Area:** ECDSA-P256 implementation exercised via
  `test/unit/lib/crypto/ecdsa_p256_spec.spl`
- **Severity:** high (verify rejects a signature this repo's own sign just
  produced — a basic round-trip break, not an edge case).
- **Status:** RESOLVED 2026-11-25 — root cause found (SPKI DER passed to a
  provider that verifies against the raw EC point) and the module rewired;
  round-trip and CAVP verify pass (see dated resolution below).
- **Do not touch the NIST CAVP vector.** (unchanged — the vector was not
  touched)

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/ecdsa_p256_spec.spl --no-session-daemon
```

```
ECDSA-P256-SHA-256 round-trip sign + verify
✓ sign returns a 64-byte signature
✗ signs and verifies an empty message
    expected false to equal true
✗ signs and verifies a short ASCII message
  (6 examples, 2 failures)

ECDSA-P256-SHA-256 NIST CAVP SigVer
✗ NIST CAVP P-256 SHA-256 vector verifies (Result = P)
```

`sign` itself produces a correctly-sized (64-byte) signature, but `verify`
called on that same fresh signature returns `false` instead of `true`.

## Root-cause hypothesis

Unlike the P-384 case (`doc/08_tracking/bug/ecc_p384_p521_sign_verify_broken_2026-07-20.md`,
where `sign` itself is broken — 0-byte output), P-256 `sign` produces
correctly-shaped output, but `verify` rejects it. Combined with the NIST
CAVP vector (verifying an externally-supplied, known-correct signature)
also failing, this points at a bug in P-256 `verify` specifically (rather
than in `sign`) — e.g. in the signature-verification equation
(`u1*G + u2*Q` recomputation), scalar/point encoding mismatch between what
`sign` emits and what `verify` expects, or a hash-to-scalar conversion bug.
Not further localized within the P-256 implementation in this triage pass.

Given P-384's CAVP verify and P-521's CAVP verify also fail (see the
sibling doc above), there is a plausible shared ECDSA-verify-core root
across all three curves — flagged as a hypothesis for a follow-up
investigation to confirm or rule out, not asserted here.

## What NOT to do

Do not touch the NIST CAVP P-256 vector.

## Affected specs

- `test/unit/lib/crypto/ecdsa_p256_spec.spl` (3 failures: 2 round-trip, 1
  CAVP verify)

## 2026-11-25 resolution (P1 fleet lane) — FIXED

**Root cause (two stacked defects):**

1. **SPKI-vs-point mismatch (the original 2026-07-20 symptom).** The runtime
   provider (`rt_ecdsa_p256_verify[_checked]`, ring
   `UnparsedPublicKey::new(&ECDSA_P256_SHA256_FIXED, pk)` —
   `src/compiler_rust/compiler/src/interpreter_extern/signatures.rs:482`)
   verifies against the RAW 65-byte uncompressed EC point
   (`04 || Qx || Qy`), but `os.crypto.ecdsa_p256.ecdsa_p256_verify_fixed`
   passed the 91-byte SPKI DER straight through. Every verify — fresh
   round-trip AND the NIST CAVP vector — therefore returned false, while
   `sign` (which takes PKCS#8, handled correctly by the provider) produced
   correctly-shaped 64-byte output. Measured directly:
   `ecdsa_p256_verify_checked(point, msg, sig) = true` vs
   `ecdsa_p256_verify_checked(spki, msg, sig) = false` on the same CAVP
   vector.
2. **Module rewound to removed externs.** The 2026-09 transplant
   `88aac2ffe28` (and the 2026-10-22 release-phase3 merge resolution)
   rewound `src/os/crypto/ecdsa_p256.spl` past both `9ec9ebf4391` and the
   `f107176ee6d` restore, leaving it importing `rt_ecdsa_p256_sign` /
   `rt_ecdsa_p256_verify`, which `signature_sffi.spl` no longer declares —
   the module could not resolve its own imports at HEAD.

**Fix** (`src/os/crypto/ecdsa_p256.spl`): the wrappers now call the checked
SFFI wrappers (`ecdsa_p256_sign_checked` / `ecdsa_p256_verify_checked`),
convert SPKI DER to the raw EC point (with the RFC 5480 header bound) before
the verify call, and keep the existing public `[u8]`/`bool` signatures every
current caller (jwt, cose, sshd, tls13, both specs) uses — Ok/Err collapses
to the documented empty-array/false-on-error contract. Importing the
common-layer `ecdsa_p256_sign/verify` by those bare names was tried first
and rejected: they collide same-signature with `signature_sffi`'s
different-body namesakes (the Class B silent-misdispatch shape of
`duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09.md`),
which made the wrapper silently run the no-conversion body. Two
`.unwrap()` stragglers in `test/01_unit/os/tls13/cert_verify_ecdsa_spec.spl`
(merge residue expecting the rewound Result API) were aligned to the
`[u8]`-returning API.

**Verification** (the named spec cannot run at HEAD — `bin/simple.exe test`
fails repo-wide on `unknown decorator '@representation_boundary'` — so the
same checks ran as a standalone interpreter probe with the spec's own key
material and CAVP vector, `SIMPLE_LIB=src SIMPLE_EXECUTION_MODE=interpret
bin/simple.exe run`, seed v1.0.0-rc.1, Windows, tip `0819b116ecb`):

| check | before | after |
|---|---|---|
| sign returns 64-byte signature | module dead (unresolvable imports) | `sig_len=64` ✓ |
| round-trip empty message | false | `rt_empty=true` ✓ |
| round-trip "hello" | false | `rt_hello=true` ✓ |
| reject under wrong public key | — | `wrong_key=false` ✓ |
| reject flipped r-byte | — | `flipped=false` ✓ |
| NIST CAVP P-256 SHA-256 vector | false | `cavp=true` ✓ |

The CAVP vector was not modified. Negative paths still reject.
