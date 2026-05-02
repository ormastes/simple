# ML-DSA-65 Sign/Verify pipeline mismatch (2026-05-02)

## Status
OPEN — filed by Wave 10 W10-A while seeding ML-DSA-65 (FIPS 204) for hybrid TLS 1.3.

## Summary
`src/os/crypto/ml_dsa.spl` produces a syntactically correct 3293-byte signature
via `ml_dsa_sign_65` (matches FIPS 204 §B size for ML-DSA-65: 32 + l*640 +
omega + k = 32 + 5*640 + 55 + 6 = 3293 bytes), but the corresponding
`ml_dsa_verify_65` rejects the signature on a ~80s smoke run with
`xi = [0..31]`, `msg = [0x42; 16]`, `rnd = [0; 32]`.

## Root-cause hypotheses (in decreasing likelihood, post-review 2026-05-02)

1. **`sample_in_ball` byte-stream refresh** — when the initial 264-byte
   SHAKE-256 output runs out of usable indices, the implementation calls
   `shake256(seed, 512)` again with the *same* seed, which re-emits the same
   first 264 bytes plus 248 new ones.  This means the loop sees the same
   already-rejected bytes a second time before reaching genuinely new data.
   For the rare case where the seed yields many high-byte values, this can
   loop or pick a different distribution than the FIPS 204 reference.  Fix:
   advance the SHAKE-256 sponge state across refresh, or generate a single
   long stream up front (e.g., 8 + 1024 bytes) and never refresh.
2. **`make_hint_poly` polarity on negative-z input** — the per-coefficient
   round-trip is unit-tested green for centred z, but the signed `-c·t0`
   first argument is reduced via `_vec_sub(_poly_vec_zero(k), ct0_coeff)`
   which lands in [0, q).  MakeHint then receives it as a positive Z_q
   element rather than a centred negative.  Verify whether MakeHint's
   `HighBits(r) != HighBits(r+z)` test agrees with sign's intent.

**Eliminated as hypotheses**: hint pack/unpack ordering (cross-checked
against FIPS 204 §B.4 HintBitPack/Unpack — sign and verify use matching
cumulative-count semantics); w1 encoding bit width (r1 ∈ [0, 16) under
validated `Decompose r1 lies in [0, 16)` invariant, 4 bits suffices).

## What works (validated by `test/unit/lib/crypto/ml_dsa_65_spec.spl`)

- NTT round-trip on arbitrary 256-coefficient polynomials over Z_q (q=8380417).
- NTT([1, 0, ..., 0]) == [1; 256] (zetas table validated against the
  generic-polynomial property).
- NTT-domain pointwise multiplication agrees with direct convolution in
  Z_q[X]/(X^256+1), including the X^255 * X = -1 negacyclic boundary.
- Power2Round, Decompose, MakeHint/UseHint round-trips at int level.
- SHAKE-128/256 against NIST FIPS 202 KAT empty-input vectors (byte-exact).
- BitPack 4-bit and 10-bit round-trips.
- SampleInBall produces exactly tau=49 nonzero coefficients in {-1, 0, +1}.
- KeyGen produces (pk, sk) of expected encoded sizes (1952B, 4032B).

## Reproduction

```
bin/simple test/unit/lib/crypto/ml_dsa_65_spec.spl
```

Standalone Sign+Verify reproduction:

```
use os.crypto.ml_dsa.{ml_dsa_keygen_65, ml_dsa_sign_65, ml_dsa_verify_65}
fn main():
    var xi = []
    var i = 0
    while i < 32:
        xi.push(i)
        i = i + 1
    val kp = ml_dsa_keygen_65(xi)
    val pk = kp[0]
    val sk = kp[1]
    var msg = []
    var m = 0
    while m < 16:
        msg.push(0x42)
        m = m + 1
    var rnd = []
    var r = 0
    while r < 32:
        rnd.push(0)
        r = r + 1
    val sig = ml_dsa_sign_65(sk, msg, rnd)
    print("sig len = " + sig.len().to_string())   # → 3293
    print("verify  = " + ml_dsa_verify_65(pk, msg, sig).to_string())  # → false
```

Wallclock: KeyGen ~18s, Sign ~60s, Verify ~5s in the interpreter.

## Remediation plan

- Add an instrumented variant that returns intermediate `w1`, `w1'`, the
  recomputed `c_tilde'`, and the original `c_tilde` so the divergence point
  is exact.
- Cross-check by signing with deterministic `rnd = 0` and dumping the
  three NTT-domain witnesses (A·z, c·t1·2^d, w'_approx) against a Python
  reference impl.
- Once root-caused, add the end-to-end Sign+Verify spec without weakening
  the algebraic invariants already in `ml_dsa_65_spec.spl`.

## Severity / urgency

- M5 post-quantum signature support is not currently in any production
  TLS path; this is a pre-integration seed.
- Wave 11+ TLS 1.3 hybrid sigalg wiring blocks on a working Sign+Verify,
  so this becomes urgent at that point.

## References

- FIPS 204 — Module-Lattice-Based Digital Signature Standard, Aug 2024.
  https://csrc.nist.gov/pubs/fips/204/final
- `src/os/crypto/ml_dsa.spl` (Algorithms 1, 2, 3)
- `src/os/crypto/ml_dsa_ntt.spl` (Algorithms 35-40, NTT)
- `src/os/crypto/ml_dsa_sample.spl` (Algorithms 22-34, SHAKE)
- `test/unit/lib/crypto/ml_dsa_65_spec.spl` (validated invariants)
- `doc/08_tracking/crypto_recovery_status.md` Wave 10 entry
