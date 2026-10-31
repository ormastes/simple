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
| `var t0` also assigned from `(x).to_u8()`, then `t0.to_i64()` | returned 0 |

Reproduction: `test/fixtures/devhub/native_codegen_repro/main.spl`, expected red on
the pinned producer. Published vectors guard the crypto:
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

## Likely owner, not yet confirmed

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` routes an unproven
receiver's `to_i64` to `rt_to_int_dynamic`. Which path produces 0 was not isolated,
and the current compiler source may behave differently from the pinned producer.

## Remaining exposure

The form `.len().to_i64()` appears in 504 places across 129 files under `src/lib`,
`src/app` and `src/compiler`. Only the SQLCipher read path was changed. Fix the
lowering and verify on a rebuilt compiler rather than editing each site.
