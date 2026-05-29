# FR: Native modular exponentiation for FFDHE 2048+ bit groups

- **Date filed:** 2026-05-02
- **Status:** OPEN — interpreter-mode 2048/3072/4096-bit round-trip KAT blocked
- **Cross-ref:** `src/os/crypto/ffdhe.spl` (pure-Simple reference impl)
- **Cross-ref:** `test/unit/os/crypto/ffdhe_kat_spec.spl`
- **Cross-ref:** `doc/02_requirements/feature/scrypt_native_runtime_helpers_2026-05-02.md`
  (sister FR — same interpreter-throughput root cause)

## Summary

FFDHE (RFC 7919) key exchange is implemented in pure Simple at
`src/os/crypto/ffdhe.spl` using an inlined square-and-multiply modexp loop
(same pattern as `rsa_fallback.spl` and `curve25519_bigint.spl`).

Algorithm correctness is verified byte-exact for small primes (p=23, g=2)
and group-prime integrity is pinned by SHA-256 fingerprint for
ffdhe2048/3072/4096 in interpreter mode.

The full Alice/Bob DH round-trip for ffdhe2048 (§5 in the KAT spec) is
marked `@slow` because the 2048-bit modexp is O(minutes) in the interpreter.
The 3072-bit and 4096-bit round-trips are omitted until this FR lands.

## Why pure-Simple optimisation is not sufficient

The pure-Simple modexp performs a square-and-multiply loop over each bit of
the exponent (~2048 iterations for ffdhe2048). Each iteration does:

```
base_mod = _f_mod(_f_mul(base_mod, base_mod), p)   # square
result   = _f_mod(_f_mul(result,   base_mod), p)   # conditional multiply
```

`_f_mul` on two 2048-bit numbers (≈69 limbs at 2^30 each) requires
69×69 = ~4761 limb multiplications. Each `_f_mod` is a bit-by-bit shift-
and-subtract loop (~2048 shift steps × 69-limb comparison).

Per-call cost (rough):
```
2048 squarings × (4761 limb-muls + 2048 mod-steps) ≈ 1.4 × 10^7 ops
```

At interpreter throughput of ~10^5–10^6 ops/s the ffdhe2048 keygen takes
roughly 15–140 seconds per call — beyond the 60 s watchdog and well beyond
the acceptable test-run budget.

## Proposed implementation

Add a `rt_modexp(base: [u8], exp: [u8], modulus: [u8]) -> [u8]` extern
backed by a constant-time GMP or `num-bigint` Rust implementation.
The pure-Simple implementation becomes the fallback for freestanding/
baremetal targets that lack the extern.

Interface sketch:
```
extern fn rt_modexp_be(base: [u8], exp: [u8], modulus: [u8]) -> [u8]
```

All inputs and output are big-endian byte arrays. The extern returns
`base^exp mod modulus` zero-padded to `modulus.len()` bytes.

## Acceptance criteria

- [ ] `rt_modexp_be` extern added to the Rust runtime with GMP/num-bigint backend
- [ ] `ffdhe.spl` updated to call `rt_modexp_be` when the extern is available,
      falling back to `_f_mod_exp` otherwise
- [ ] KAT spec §5 ffdhe2048 round-trip passes without `@slow` in native mode
- [ ] ffdhe3072 and ffdhe4096 round-trip KAT vectors added and passing
- [ ] RSA fallback (`rsa_fallback.spl`) migrated to the same extern
