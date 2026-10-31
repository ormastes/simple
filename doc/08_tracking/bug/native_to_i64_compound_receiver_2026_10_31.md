# Native `.to_i64()` returns 0 on a compound receiver

Status: FIXED in source by `8d261cef11b`; not confirmed on a rebuilt compiler.
Severity: P0 for binaries from the old producer. Date: 2026-10-31.

## Symptom

Built by the pinned Phase 2 producer (SHA-256 `13d73267...`, source `fa967a99dcb`,
Oct 25), `.to_i64()` returns 0 for every non-zero input on some receivers, silently:

| Receiver | Result over inputs 0..255 |
| --- | --- |
| `arr.len().to_i64()` | wrong for all 255 non-zero inputs |
| `((w + 1) - 1).to_i64()` | wrong for all 255 non-zero inputs |
| `u8_of(v).to_i64()` | correct |
| typed local `n.to_i64()` | correct |
| `t0.to_i64()` in `aes_gcm.spl`, where `t0` also takes a compound assignment | inferred 0 from the key schedule; not reproduced in a minimal fixture |

Reproduction: `test/fixtures/devhub/native_codegen_repro/main.spl`, red on the pinned
producer for the first two rows.

## Cause

The receiver had no numeric proof, so `method_calls_literals.spl` treated it as text
and emitted the text parse (`rt_string_to_int_lenient`), which yields 0 for a small
integer word. Commit `8d261cef11b` (Oct 27) fixed that lowering, and the producer
predates it. An A/B on MIR callees confirmed the fix's effect in interpreter mode. The
runtime path to 0 was read in source, not executed.

## Consequences found

- `sqlcipher4_keys.spl`: `passphrase.len().to_i64() == 0` was always true, so every
  key session failed with `SQLCIPHER4_MISSING_SECRET`.
- `aes_gcm.spl`: the Rcon index was always 0, and `t0` in the AES-256 `m == 4` branch
  was read as 0. The key schedule was wrong but self-consistent, so round trips passed
  while real ciphertext decrypted to garbage. Only known-answer vectors expose this.
- Wipes: `_sqlcipher4_zeroize_u8` read a length of 0, so it reported success without
  wiping anything on Phase 2.
- Data: anything a Phase 2 binary encrypted with the old key schedule no longer
  decrypts after the fix. It fails closed. Stored data was not audited.

## Open

- `native_codegen_repro` has not run on a rebuilt compiler.
- `8d261cef11b` does not explain the `t0` row, so keep the `aes_gcm.spl` workaround
  until the vectors pass without it on a rebuilt compiler.
- Binaries from the old producer stay exposed at about 500 `.len().to_i64()` sites.
