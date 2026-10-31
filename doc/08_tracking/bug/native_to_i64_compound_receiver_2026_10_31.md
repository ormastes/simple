# Native `.to_i64()` returns 0 on a compound or unproven receiver

Status: OPEN for the compiler; the SQLCipher read path is worked around.
Severity: P0 (silent wrong values). Date: 2026-10-31.

## Symptom

Built by the pinned Phase 2 producer (SHA-256 `13d73267...`), `.to_i64()` returns
0 for every non-zero input on some receivers, with no error:

| Receiver | Result over inputs 0..255 |
| --- | --- |
| `arr.len().to_i64()` | wrong for all 255 non-zero inputs |
| `((w + 1) - 1).to_i64()` | wrong for all 255 non-zero inputs |
| `u8_of(v).to_i64()` | correct |
| typed local `n.to_i64()` | correct |
| `t0.to_i64()` in `aes_gcm.spl`, where `t0` also takes a compound assignment | inferred 0 from the key schedule; not reproduced in a minimal fixture |

Reproduction: `test/fixtures/devhub/native_codegen_repro/main.spl`, red on the pinned
producer for the first two rows (255 of 256 wrong each). Published vectors guard the crypto:
`test/fixtures/devhub/native_crypto_kat/main.spl` (11/11 pass on Phase 2 after the
workaround). Phase 1 specs pass on these forms.

## Consequences found

- `sqlcipher4_keys.spl`: `passphrase.len().to_i64() == 0` was always true, so every
  key session failed with `SQLCIPHER4_MISSING_SECRET`. This was the Phase 2 cause
  of `devhub_secured_db_key_session_open_failure_2026_10_27.md`.
- `aes_gcm.spl`: the Rcon index was always 0, and `t0` in the AES-256 `m == 4`
  branch was read as 0. The key schedule was wrong but self-consistent, so
  round trips passed while real ciphertext decrypted to garbage. Only known-answer
  vectors expose this class.

- Wipes: `_sqlcipher4_zeroize_u8` read a length of 0, so it reported success without
  wiping anything on Phase 2.
- Data: anything a Phase 2 binary encrypted with the old key schedule no longer
  decrypts after the fix. It fails closed. Stored data was not audited.

## Likely owner, not yet confirmed

`native_to_i64_on_binop_receiver_miscompile_2026-10-27.md` is marked FIXED for this
area, and the pinned producer may predate that fix. Check a rebuilt compiler first.

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` routes an unproven
receiver's `to_i64` to `rt_to_int_dynamic`. Which path produces 0 was not isolated,
and the current compiler source may behave differently from the pinned producer.

## Remaining exposure

The form `.len().to_i64()` appears in about 500 places under `src/lib`, `src/app` and
`src/compiler`, and compound receivers are also exposed. Only the SQLCipher read path
was changed. Fix the lowering and verify on a rebuilt compiler rather than editing
each site.
