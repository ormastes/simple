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

## Update 2026-11-19 (milestone_0043, Opus re-review B P2-2/P2-3/P3-6/P3-7; source-authored, NOT_RUN)
The std internals above are not the only unwiped copies, and earlier text understated that. Status per copy in
`src/app/orchestrator/host_identity_key_v1.spl`:
- Fixed: the base64 decoder kept its four pending sextets in a fresh `[i64]` each quad (about 86 dropped arrays per
  key file). It now uses one 4-byte `[u8]`, resets it in place, and wipes it (checking the wipe) on every exit. A failed
  decoder wipe returns `host-identity-key-buffer-wipe` instead of a silent `[]`.
- Fixed: encode built the base64 body as text and the PEM as a growing text, about six prefixes of the private body.
  `host_identity_pem_encode_v1` now writes the armour straight into one pre-sized `[u8]`. The output is byte-identical
  (spec ENCWIPE-08).
- Fixed (P3-7): the armour layout is canonical. Every line is 70 characters except a non-empty last line, LF-terminated.
- OPEN: `host_identity_key_generate_v1` receives the 36 entropy bytes as immutable hex TEXT from `sosix_random_hex`.
  That is a plaintext copy of the seed and check, and it cannot be wiped. The only entropy API returns text. Removing
  this copy needs a bytes-returning entropy extern, which is a runtime change and is not made here.
- OPEN: the returned private file `[u8]` is the caller's key-file buffer. Whether it is wiped after it is written is the
  caller's decision (`host_identity_command_v1.spl`).
- OPEN (not in this change): store-read error paths in `host_identity_command_v1.spl` drop `bytes` unwiped (REVIEW_B
  P3-11).
