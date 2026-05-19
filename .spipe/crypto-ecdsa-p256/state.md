# ECDSA P-256 Crypto Module

## Phases
- [x] research — 2026-05-19: rt_ecdsa_p256_sign + rt_ecdsa_p256_verify already registered interpreter externs (Path A). signature_sffi.spl has SSH-layer wrappers; common/crypto/ needs a pure-common thin wrapper mirroring hmac.spl.
- [x] implement — 2026-05-19: src/lib/common/crypto/ecdsa_p256.spl — extern declarations + sign/verify wrappers + _unwrap_sig coercion. NOTE: spec file was absent at end of prior session despite state claiming otherwise; created in verify phase below.
- [x] verify — 2026-05-19: DEFERRED-BLOCKED. Spec created (9 tests: 6 sign+verify round-trip, 3 NIST CAVP verify-only). Syntax bug fixed (0xce u8 → 0xceu8 on line 38). Test runner blocked by pre-existing parse errors in src/compiler_rust/lib/std/src/tooling/testing/parallel.spl (Unexpected token: DoublePipe) and filter.spl (Unexpected token: RBrace); all bin/simple test invocations exit 3 with zero output. Spec file is syntactically clean (no grep hits for `0x.. u8`).
- [ ] ship — deferred pending test runner fix
