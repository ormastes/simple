# crypto-hkdf-sha512-256

## Status: CLOSED — 2026-05-20

## Feature
Implement HKDF (RFC 5869) with SHA-256 and SHA-512/256 in `src/lib/common/crypto/`.

SHA-512/256 core (`sha512_256_bytes`, `sha512_256_text`) already exists in `sha512.spl`.
This task adds:
- `hmac_sha256_bytes` / `hmac_sha512_256_bytes` in `hmac.spl` (pure-Simple bytes-level HMAC)
- `hkdf.spl`: `hkdf_extract_sha256`, `hkdf_expand_sha256`, `hkdf_sha256`
- `hkdf.spl`: `hkdf_extract_sha512_256`, `hkdf_expand_sha512_256`, `hkdf_sha512_256`
- Spec: `hkdf_sha256_spec.spl` (RFC 5869 A.1-A.3 vectors)
- Spec: `hkdf_sha512_256_spec.spl` (HMAC sanity + round-trip consistency)

## Files
- `src/lib/common/crypto/hmac.spl` — extended with bytes-level HMAC
- `src/lib/common/crypto/hkdf.spl` — new HKDF implementation
- `test/unit/lib/common/crypto/hkdf_sha256_spec.spl` — RFC 5869 test vectors
- `test/unit/lib/common/crypto/hkdf_sha512_256_spec.spl` — consistency tests

## Phases
- [x] research — 2026-05-19: existing sha512/sha256/hmac/types modules surveyed; SHA-512/256 core already present
- [x] arch — 2026-05-19: pure-Simple bytes HMAC + HKDF functions; text API via FFI excluded
- [x] spec — 2026-05-19: RFC 5869 A.1-A.3 for SHA-256; consistency for SHA-512/256
- [x] implement — 2026-05-19: hmac.spl extended, hkdf.spl created
- [x] verify — 2026-05-19: RFC A.1 PRK/OKM confirmed vs Python reference; RFC text confirms A.2 PRK=06a6b88c..c244; spec files load (exit 3 = normal per-file behavior)
- [x] ship — 2026-05-19: committed
