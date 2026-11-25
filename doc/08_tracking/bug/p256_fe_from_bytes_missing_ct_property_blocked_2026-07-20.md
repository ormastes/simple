# P-256 `ecdh_p256.spl` calls `fe_from_bytes`, which has no P-256-field implementation

- **Date:** 2026-07-20
- **Area:** `src/os/crypto/ecdh_p256.spl`
- **Severity:** high (blocks all 4 examples in the P-256 constant-time
  property spec — including the structural CT check itself, so the
  underlying CT property of P-256 scalar-mul is currently **unverified**,
  not merely unverifiable-and-passing).
- **Status:** RESOLVED 2026-11-25 — `fe_from_bytes` for the P-256 field now
  exists and the exact symptom no longer reproduces (probe below).

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/p256_ct_property_spec.spl --no-session-daemon
```

```
✗ derives the same public key when called twice on the same scalar (determinism)
    semantic: function `fe_from_bytes` not found
✗ two scalars differing in one bit produce distinct public keys (k=1 vs k=2)
    semantic: function `fe_from_bytes` not found
✗ low-Hamming-weight scalar (0x00..0x01) produces a valid 65-byte SEC1 point
    semantic: function `fe_from_bytes` not found
✗ high-Hamming-weight scalar (0xFF * 32) produces a valid 65-byte SEC1 point
    semantic: function `fe_from_bytes` not found
```

All 4 examples in the file fail identically (5 examples, 4 failures per the
baseline run — the 5th, structural-source-inspection example, was not
reached in this cluster's log).

## Root-cause hypothesis

`src/os/crypto/ecdh_p256.spl:51` imports `fe_from_bytes, fe_to_bytes` and
calls `fe_from_bytes(px_bytes)` / `fe_from_bytes(py_bytes)` at
`ecdh_p256.spl:319-320` inside `p256_keypair_pub`, the function the spec
exercises. `fe_from_bytes` exists for **other** curves —
`src/lib/common/crypto/ed25519.spl:454` (`Fe25519`),
`src/os/crypto/p384_field.spl:181` (`Fe384`),
`src/os/crypto/curve25519.spl:289` (`Fe25519`) — but there is no P-256-field
(`Fe256`-equivalent) `fe_from_bytes` anywhere in the tree
(`grep -rn "^fn fe_from_bytes" src/lib/common/crypto/ src/os/crypto/` returns
only the three files above). Either `ecdh_p256.spl` is importing from the
wrong module (aliasing another curve's field type incompatibly), or the
P-256 field module never got a `fe_from_bytes` defined at all.

This is a library-internal call inside `os.crypto.ecdh_p256`, not a spec
import issue — the spec only imports `p256_keypair_pub` itself
(`use os.crypto.ecdh_p256.{p256_keypair_pub}`), so there is no test-side fix
available.

## What NOT to do

Do not weaken/remove the 4 `expect(...)` blocks to force green — the
underlying P-256 constant-time property is genuinely unverified while this
blocks the file, which is worse than a red test.

## Affected specs

- `test/unit/lib/crypto/p256_ct_property_spec.spl` (4 of 5 examples; the
  5th, structural source-inspection example was not exercised in this run)

## Verification 2026-11-25 (p2w4-al lane, Windows host)

The missing-function defect is gone at release/1.0.0 HEAD:

- `src/os/crypto/ecdh_p256.spl:46-53` imports `fe_from_bytes, fe_to_bytes`
  from `std.common.math.field.fe_p256`, and that module defines
  `fn fe_from_bytes(bytes: [u8]) -> FeP256` at
  `src/lib/common/math/field/fe_p256.spl:337` — the P-256-field
  implementation whose absence this bug records.
- Live probe (seed interpreter, `SIMPLE_LIB=src bin/simple.exe run`): a
  driver calling `p256_keypair_pub` on scalar 0x00..0x01 printed
  `pub len=65 deterministic=true` — the exact call path
  (`fe_from_bytes(px_bytes)`/`(py_bytes)` inside `p256_keypair_pub`) executes
  and yields a valid 65-byte SEC1 point, deterministically.

The spec has moved to `test/01_unit/lib/crypto/p256_ct_property_spec.spl`;
running it was environment-blocked (`bin/simple.exe test` cannot load the
tree: `unknown decorator '@representation_boundary'` in
`src/app/test_runner_new/test_runner_client.spl` — known release/1.0.0
source/binary inconsistency). The constant-time property assertions
themselves were not re-executed here; closure covers the filed defect
(`fe_from_bytes` not found), which is verifiably fixed.
