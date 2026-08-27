# X25519MLKEM768 pure-Simple ownership audit — 2026-08-12

## Result

The scalar cryptographic algorithm is owned by Simple source, but the complete
execution stack is not boundary-free and must not be described as wholly
pure-Simple runtime code.

- `src/os/crypto/ml_kem.spl`, `ml_kem_kpke.spl`, and `ml_kem_ntt.spl` own the
  FIPS 203 FO transform, K-PKE, SHAKE composition, sampling, encoding, scalar
  NTT, and constant-work implicit rejection in Simple.
- `src/os/crypto/curve25519_bigint.spl` and `curve25519_smalllimb.spl` own the
  RFC 7748 ladder and field arithmetic in Simple. The public wrapper calls the
  `rt_bytes_u8_at` extern only to read the `[u8]` representation; that runtime
  accessor is a representation boundary, not a foreign X25519 implementation.
- The scalar TLS path composes those Simple owners in
  `src/os/crypto/x25519_mlkem768/hybrid.spl`. TLS entropy separately crosses
  the canonical platform entropy facade; entropy is not implemented by the
  deterministic KEM functions.
- `std.simd` owns SIMD feature detection and batch dispatch. CUDA, Metal, and
  Vulkan candidates cross explicit `Crypto*Session` device/runtime boundaries
  and offload only NTT batches. FO selection, wire validation, X25519, and the
  hybrid combiner remain CPU-side Simple code. These candidates are not proof
  that the full algorithm is pure-Simple or production-promoted.

## Correctness gap closed

`ml_kem_768_decapsulation_key_valid` previously checked the embedded public
key and its stored hash but accepted non-canonical coefficients in the first
1152-byte private K-PKE polynomial vector. The checked API now validates all
three private polynomials before decapsulation. The focused native-tagged-value
spec constructs an otherwise valid key, encodes `q = 3329` in the private
prefix, and requires rejection independently of the embedded-key hash.

## Evidence status

Source inspection and the focused regression are present. No compiler/test or
performance result is claimed by this audit: the admitted self-hosted compiler
was unavailable in this session. Existing KAT, hybrid-oracle, TLS integration,
SIMD, and device evidence remain the authoritative executable gates when that
compiler is available. GPU measurements are explicitly outside this audit.
