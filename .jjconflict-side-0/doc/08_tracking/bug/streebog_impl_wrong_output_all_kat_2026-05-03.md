# Bug — `src/os/crypto/streebog.spl` produces wrong output for all Streebog KAT vectors

**Filed:** 2026-05-03
**Resolved:** 2026-05-08
**Resolution:** Implementation was already correct. The spec file had wrong expected
values (wrong byte order / stale vectors). Fixing the spec vectors made all KAT tests pass.

## Symptom (original)

`test/unit/os/crypto/streebog_kat_spec.spl` had hash-comparison assertions failing
under the old wrong expected values. The implementation itself was not the cause.

## Verification (2026-05-08)

All RFC 6986 KAT vectors verified correct against `gostcrypto` Python reference:

| Input | Variant | Implementation output | Status |
|---|---|---|---|
| `""` | 256 | `3f539a213e97c802cc229d474c6aa32a825a360b2a933a949fd925208d9ce1bb` | PASS |
| `""` | 512 | `8e945da209aa869f0455928529bcae4679e9873ab707b55315f56ceb98bef0a7362f715528356ee83cda5f2aac4c6ad2ba3a715c1bcd81cb8e9f90bf4c1c1a8a` | PASS |
| `"01234...012"` (63 bytes) | 256 | `9d151eefd8590b89daa6ba6cb74af9275dd051026bb149a452fd84e5e57b5500` | PASS |
| `"01234...012"` (63 bytes) | 512 | `1b54d01a4af5b9d5cc3d86d68d285462b19abc2475222f35c085122be4ba1ffa00ad30f8767b3a82384c6574f024c311e2a481332b08ef7f41797891c1646f48` | PASS |
| RFC 6986 Cyrillic vector | 256 | `9dd2fe4e90409e5da87f53976d7405b0c0cac628fc669a741d50063c557e8f50` | PASS |
| RFC 6986 Cyrillic vector | 512 | `1e88e62226bfca6f9994f1f2d51569e0daf8475a3b0fe61a5300eee46d961376035fe83549ada2b8620fcd7c496ce5b33f0cb9dddc2b6460143b03dabac9fb28` | PASS |

`bin/simple test test/unit/os/crypto/streebog_kat_spec.spl` → **7 passed, 0 failed**.

## Correction to original root-cause analysis

The original suspected root causes were **incorrect**:

1. **`_g_N` / `_streebog_encrypt` analysis was wrong.** The bug doc claimed the
   loop misorders round-key XOR. The actual code at line 740 is
   `k = _lps(_state_xor(k, ci))` which is exactly the RFC 6986 §6 key schedule.
   The initial LPS on K is correctly applied in `_g_N` (line 756) before passing
   to `_streebog_encrypt`. Do not change this code.

2. **L-transform MDS matrix is correct.** The 64-row × 8-byte table in
   `_streebog_a_rows` produces correct output. The described `% 8 vs % 64` concern
   was based on an old version of the code that no longer exists.

3. **Output byte extraction is correct.** The state is stored as a flat 64-byte
   list; `h.get(j)` is correct. Streebog-256 takes `h[32..64]` (the most-significant
   half in the little-endian representation used by the implementation).

## What was actually wrong

The `test/unit/os/crypto/streebog_kat_spec.spl` expected values were stale/wrong.
The spec was updated with correct RFC 6986 vectors verified against `gostcrypto`.

## Related

- `test/unit/os/crypto/streebog_kat_spec.spl` — KAT spec (now correct, 7/7 pass)
- `src/os/crypto/streebog.spl` — implementation (correct, no changes needed)
- RFC 6986 §7.1, §6.4 — normative reference
