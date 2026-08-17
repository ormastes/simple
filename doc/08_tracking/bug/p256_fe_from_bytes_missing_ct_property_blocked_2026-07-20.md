# P-256 `ecdh_p256.spl` calls `fe_from_bytes`, which has no P-256-field implementation

- **Date:** 2026-07-20
- **Area:** `src/os/crypto/ecdh_p256.spl`
- **Severity:** high (blocks all 4 examples in the P-256 constant-time
  property spec — including the structural CT check itself, so the
  underlying CT property of P-256 scalar-mul is currently **unverified**,
  not merely unverifiable-and-passing).
- **Status:** ALREADY FIXED — verified by content 2026-08-17, no change made
  by this lane.

## Verification 2026-08-17 (classified by content, not by commit)

`src/lib/common/math/field/fe_p256.spl` **exists on disk** and provides
`fe_from_bytes`, so the import at `src/os/crypto/ecdh_p256.spl:46` resolves
and the spec loads. Measured with `bin/simple run
test/01_unit/lib/crypto/p256_ct_property_spec.spl --no-session-daemon`:

| | |
|---|---|
| this doc's claim | all 4 examples blocked, spec unrunnable |
| measured 2026-08-17 | `executed=5 passed=5 failed=0`, rc=0 |

The structural CT check (`_scalar_mul_affine` body contains no `if` branch on
a scalar bit) now executes and passes, so the CT property this doc flagged as
"unverified, not merely unverifiable-and-passing" is now actually verified.
No source change was required; the blocker was resolved upstream.

**Scope note:** the sibling row
`p256_stack_imports_nonexistent_fe_p256_module_2026-08-04.md` is the same root
cause and is marked `CLAIMED-OFFHOST 2026-08-17`. This lane deliberately made
**no edit** to any P-256 source file, so that host's ablation evidence is
intact; the above is a read-only measurement.

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
