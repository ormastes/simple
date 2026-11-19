# std ed25519 leaves secret temporaries unwiped (2026-11-19)

Status: OPEN (NOT_RUN, no runnable binary). Residual of `doc/08_tracking/bug/host_identity_private_parser_seed_copies_unwiped_2026-11-18.md`.

`src/lib/common/crypto/ed25519.spl`: `ed25519_pubkey` and `pure_ed25519_sign` keep the SHA-512 digest of the seed
(`h`), the clamped scalar (`a`), the nonce prefix, `r`, and field/scalar limb temporaries (`ed_scalar_mul_basepoint`,
`ed25519_field.spl`, `ed25519_scalar.spl`) as plain `[u8]`/integer values that are never passed to
`secure_zero_u8_slots`. The caller (`host_identity_key_v1.spl`) wipes every buffer it owns (seed, check, entropy
bytes, body, raw) but cannot reach these.

Not fixed in the host-identity lane: the temporaries are spread across SHA-512, scalar reduction and point
multiplication (limb arrays and i64 intermediates with no wipe primitive for integer locals), so a contained change
is not possible. Fix needs a std-level pass: wipe `h`/`a`/prefix `[u8]` buffers at the end of each entry point and
decide the policy for limb temporaries. Needs a spec that cannot observe locals today, so it also needs a test hook.
