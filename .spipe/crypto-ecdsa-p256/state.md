# ECDSA P-256 Crypto Module

## Phases
- [x] research — 2026-05-19: rt_ecdsa_p256_sign + rt_ecdsa_p256_verify already registered interpreter externs (Path A). signature_sffi.spl has SSH-layer wrappers; common/crypto/ needs a pure-common thin wrapper mirroring hmac.spl.
- [x] implement — 2026-05-19: src/lib/common/crypto/ecdsa_p256.spl — extern declarations + sign/verify wrappers + _unwrap_sig coercion; src/lib/common/crypto/ecdsa_p256_spec.spl — known-answer smoke tests.
- [ ] verify — run `bin/simple test src/lib/common/crypto/ecdsa_p256_spec.spl`
- [ ] ship
