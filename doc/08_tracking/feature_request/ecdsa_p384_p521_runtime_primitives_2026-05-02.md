# Feature Request: ECDSA-P-384 + ECDSA-P-521 primitives for TLS 1.3

**Filed:** 2026-05-02
**Filed by:** W11-C (TLS 1.3 sigalg coverage track)
**Modules:**
- `src/lib/nogc_sync_mut/io/signature_ffi.spl` (FFI extern path)
- `src/os/crypto/ecdh_p384.spl`, `ecdsa_p384.spl`, `ecdh_p521.spl`,
  `ecdsa_p521.spl` (pure-Simple path)
- `src/lib/common/math/field/fe_p384.spl`, `fe_p521.spl`
- `src/os/tls13/cert_verify.spl` (dispatch site, lines 784-789 + 678-680)
- `src/os/tls13/handshake13.spl` (`_build_ext_sig_algs`, line 383)
**Severity:** P2 (TLS 1.3 RFC 8446 §4.2.3 sigalg coverage; ECDSA-P-256
+ Ed25519 + RSA-PSS already cover the common case).
**Status:** OPEN

## Context

RFC 8446 §4.2.3 SignatureScheme registry for TLS 1.3 includes:

| Code   | Scheme                       | Status in tree |
|--------|------------------------------|----------------|
| 0x0403 | `ecdsa_secp256r1_sha256`     | Implemented (FFI; `ecdsa_p256.spl`) |
| 0x0503 | `ecdsa_secp384r1_sha384`     | **MISSING — typed-Err** |
| 0x0603 | `ecdsa_secp521r1_sha512`     | **MISSING — typed-Err** |
| 0x0807 | `ed25519`                    | Implemented (FFI) |
| 0x0808 | `ed448`                      | MISSING — separate FR |
| 0x0804 | `rsa_pss_rsae_sha256`        | Implemented (FFI) |
| 0x0805 | `rsa_pss_rsae_sha384`        | Implemented (FFI) |
| 0x0806 | `rsa_pss_rsae_sha512`        | Implemented (FFI) |

`src/os/tls13/cert_verify.spl` lines 784-789 already return a typed
`CertVerifyResult.Err(msg: "ecdsa_secpNNNr1_shaNNN unsupported (P-NNN
primitive not in tree)")` for the missing curves, so the current state
is honest: a peer who sends a P-384 or P-521 CertificateVerify gets a
deterministic Err, never a silent pass.

`_build_ext_sig_algs` at line 383 of `handshake13.spl` advertises
**only** `SIG_ED25519` (0x0807) today; the missing schemes are NOT
advertised, which is the correct posture — advertising a sigalg the
peer may pick and then rejecting their CertificateVerify is a
handshake break, strictly worse than not advertising.

## Why this is filed instead of implemented

The task brief assumed `ecdsa_p256.spl` is pure-Simple and could be
mirrored. It is **not** — the file's own header reads
"Hosted-only: requires the runtime crypto backend", and every
operational entry point delegates to `rt_ecdsa_p256_{sign,verify}`
externs declared in `src/lib/nogc_sync_mut/io/signature_ffi.spl`.
Only `ecdh_p256.spl` (key-agreement, public-only on the wire today) is
pure-Simple, and it leans on `src/lib/common/math/field/fe_p256.spl`
which is itself ~600 LOC of constant-time field arithmetic.

A faithful pure-Simple implementation of ECDSA-P-384 + ECDSA-P-521
therefore requires, before any signature code is written:

1. `src/lib/common/math/field/fe_p384.spl` — 6×64-bit limb GF(p) for
   `p = 2^384 − 2^128 − 2^96 + 2^32 − 1` with constant-time Solinas
   reduction (~600 LOC mirroring `fe_p256.spl`).
2. `src/lib/common/math/field/fe_p521.spl` — 9×64-bit limb GF(p) for
   the Mersenne prime `p = 2^521 − 1` (~700 LOC; the 521-bit width
   does not divide evenly into 64-bit limbs, so either a 9×58-bit or
   8×64+1×9 representation is required for constant-time reduction
   without a partial-limb wraparound footgun).
3. `src/os/crypto/ecdh_p384.spl` + `ecdh_p521.spl` — Jacobian scalar
   multiplication mirroring the always-add-and-select CT discipline
   added to `ecdh_p256.spl` on 2026-05-01 (FR
   `p256_scalar_mult_constant_time_2026-05-01.md`).
4. `src/os/crypto/ecdsa_p384.spl` + `ecdsa_p521.spl` — full ECDSA
   sign/verify per FIPS 186-5 §6 with deterministic-k per RFC 6979
   (note: even P-256 ECDSA today uses runtime random k, NOT RFC 6979,
   so a pure-Simple deterministic-k implementation would be a
   strict gain over the current P-256 path).

The combined cost is ~2,500-3,000 LOC of cryptographic code that
**must** be constant-time on secret-scalar paths
(`feedback_no_coverups.md`, `p256_scalar_mult_constant_time_2026-05-01.md`).
Interpreter-mode timing for a single P-521 scalar multiplication is
expected to be in the multi-second range based on the P-256 cost
profile and the 2× width factor on each limb operation; this exceeds
the per-test budget of `bin/simple test` and would push at least the
P-521 spec onto the compile-mode track that
`feedback_compile_mode_false_greens.md` explicitly warns against until
R2-broader lands.

This is not work that fits in a single TLS-1.3-coverage track session
without either a parallel runtime-FFI shortcut (Option A below) or a
multi-week pure-Simple effort (Option B).

## Required Changes

Two implementation paths are listed; either independently closes the
sigalg-coverage gap. Path A is roughly an order of magnitude smaller
in pure-Simple LOC and matches the current `ecdsa_p256.spl` posture;
Path B is the pure-Simple path consistent with the broader
"impl in Simple unless big perf differences" project rule.

### Path A — runtime FFI primitives (mirrors current P-256 posture)

1. Declare new externs in
   `src/lib/nogc_sync_mut/io/signature_ffi.spl`:

   ```
   extern fn rt_ecdsa_p384_verify(pubkey: [u8], message: [u8], signature: [u8]) -> i64
   extern fn rt_ecdsa_p384_sign(pkcs8: [u8], message: [u8]) -> [u8]
   extern fn rt_ecdsa_p521_verify(pubkey: [u8], message: [u8], signature: [u8]) -> i64
   extern fn rt_ecdsa_p521_sign(pkcs8: [u8], message: [u8]) -> [u8]
   ```

   Wire signatures: 96-byte `r||s` for P-384 (48+48), 132-byte `r||s`
   for P-521 (66+66 with the 521-bit values left-padded into 528-bit
   buffers, big-endian; matches RFC 8446 §4.2.3 wire form).

2. Implement the externs in `src/runtime/...` over the existing
   crypto backend (the same backend that provides the P-256 path).

3. Add pure-Simple thin wrappers `src/os/crypto/ecdsa_p384.spl` and
   `ecdsa_p521.spl` mirroring `ecdsa_p256.spl`'s `*_sign_fixed` /
   `*_verify_fixed` shape, plus DER-SEQUENCE↔fixed-r||s helpers
   (the DER encoder for P-256 already lives in `cert_verify.spl` as
   `_ecdsa_p256_der_sig_to_fixed64` and would just take a
   parameterised component-width).

4. Bootstrap rebuild required after extern additions
   (`feedback_extern_bootstrap_rebuild.md`).

### Path B — pure-Simple primitives (long-form)

1. `src/lib/common/math/field/fe_p384.spl` (NIST P-384, 6×64-bit
   limbs, Solinas reduction per FIPS 186-5 §D.1.2.4).
2. `src/lib/common/math/field/fe_p521.spl` (NIST P-521, Mersenne
   prime, 9-limb representation per FIPS 186-5 §D.1.2.5; care for the
   521-bit-into-9×64 bit-budget).
3. `src/os/crypto/ecdh_p384.spl` + `ecdh_p521.spl` mirroring the
   `ecdh_p256.spl` always-add-and-select Jacobian scalar mult.
4. `src/os/crypto/ecdsa_p384.spl` + `ecdsa_p521.spl` with RFC 6979
   deterministic-k (closes a separate gap noted at
   `test/unit/lib/crypto/ecdsa_p256_spec.spl` line 18 — P-256 today
   uses random k, not RFC 6979).
5. NIST CAVP KAT spec coverage; expect interpreter-mode wall-time
   in the multi-second range per P-521 sign/verify and budget
   accordingly (compile-mode runs are gated on
   `feedback_compile_mode_false_greens.md` resolution).

### Wiring for either path

Once the primitive lands (A or B), the dispatch site changes are:

* `src/os/tls13/cert_verify.spl` lines 784-789: replace the typed
  `Err("... primitive not in tree")` with the actual verify call
  parameterised on width + hash (SHA-384 for P-384, SHA-512 for P-521;
  the SHA primitives are already in tree at `src/os/crypto/sha512.spl`).
  Update the matching cert-chain dispatch at line 512 if it exists.
* `src/os/tls13/handshake13.spl`:
  - Add `SIG_ECDSA_P384: u16 = 0x0503` and `SIG_ECDSA_P521: u16 =
    0x0603` named constants beside the existing `SIG_ED25519`.
  - Extend `_build_ext_sig_algs` from the single-element list
    `[SIG_ED25519]` to a multi-element list including the new
    schemes (the list-length math at lines 387-389 already handles
    arbitrary-length lists; the current 1-element case is just a
    coincidence of today's coverage).
  - Server-side `select_sig_alg` (search for the ClientHello
    parser at line 1249-1271 / CertificateRequest parser) needs to
    advertise the matching scheme on outgoing CertificateRequest.
* Test coverage: `test/unit/lib/crypto/ecc_p384_p521_kat_spec.spl`
  with NIST CAVP vectors per curve.

## Why we are NOT advertising 0x0503 / 0x0603 in `_build_ext_sig_algs` today

Adding the codes to the advertised `signature_algorithms` extension
**before** the verify path can succeed would break interop: a peer
permitted to pick `ecdsa_secp384r1_sha384` from our list would then
have their `CertificateVerify` rejected on our side with the typed-Err
above, terminating the handshake. The current "advertise nothing we
cannot verify" posture is the conservative one and matches RFC 8446
§4.2.3's "the sender MUST be able to verify each algorithm it lists"
guidance.

The named TLS sigalg constants (`SIG_ECDSA_P384` / `SIG_ECDSA_P521`)
may be added separately, with a comment that they are
decode-recognised (i.e. won't crash a parser if a peer mentions them
in their advertised list) but NOT included in our outgoing
advertisement until this FR closes. See the companion small commit
landing those named constants alongside this FR.

## References

* RFC 8446 §4.2.3 (TLS 1.3 SignatureScheme registry)
* RFC 8446 §4.4.3 (CertificateVerify)
* FIPS 186-5 §6 (ECDSA), §D.1.2.4 (P-384 parameters), §D.1.2.5 (P-521)
* NIST SP 800-186 (Recommendations for Discrete Logarithm-based
  Cryptography: Elliptic Curve Domain Parameters)
* RFC 6979 (Deterministic Usage of the DSA and ECDSA)
* `doc/08_tracking/feature_request/p256_scalar_mult_constant_time_2026-05-01.md`
  (CT discipline reference for any pure-Simple primitive added under
  this FR's Path B)
* `feedback_no_coverups.md` — no skip(), no weakened assertions,
  no stub-pass `ecdsa_p384.spl` that compiles but doesn't actually
  sign/verify. Either it's a real primitive or it stays as a typed
  Err with the FR linked from the dispatch site comment.
* `feedback_compile_mode_false_greens.md` — interpreter-mode-only for
  the pure-Simple path until R2-broader lands.
