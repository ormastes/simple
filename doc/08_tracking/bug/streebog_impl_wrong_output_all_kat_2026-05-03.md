# Bug — `src/os/crypto/streebog.spl` produces wrong output for all Streebog KAT vectors

**Filed:** 2026-05-03
**Severity:** Critical — implementation is non-functional; every hash comparison
fails against the RFC 6986 / gostcrypto reference values.

## Symptom

`test/unit/os/crypto/streebog_kat_spec.spl` has 5 tests; 3 hash-comparison
assertions all fail under interpreter mode.  The digest-length checks (2/5)
pass because they only inspect `len()`.

Actual vs. expected (gostcrypto reference):

| Input | Variant | Implementation output | Correct value |
|---|---|---|---|
| `""` | 512 | `9fc88b349f71ce5345e834ba893e121a1cd815a87b3fab7f43fee3a4114bb08a22d454f84b8efa5526f7736e005cb337adb8c4094e995b7544f47ea6c1b70b2a` | `8e945da209aa869f0455928529bcae4679e9873ab707b55315f56ceb98bef0a7362f715528356ee83cda5f2aac4c6ad2ba3a715c1bcd81cb8e9f90bf4c1c1a8a` |
| `""` | 256 | `4ae8c3e38d4293bf28d29e54afecf1576a0daf89ddfd27ca3cd787996728f72b` | `3f539a213e97c802cc229d474c6aa32a825a360b2a933a949fd925208d9ce1bb` |
| `"01234...012"` (63 bytes) | 512 | `92e8cc56b4316ab50c729bf46ed89880653bd92aa2c8e7f354bd76b4eda1137a35c13a7bcd7cb5c9b7c1e342c2806b0e010aa4e33e45adae79da38da4e40c23a` | `1b54d01a4af5b9d5cc3d86d68d285462b19abc2475222f35c085122be4ba1ffa00ad30f8767b3a82384c6574f024c311e2a481332b08ef7f41797891c1646f48` |

Reference values cross-checked against:
- `gostcrypto` Python library (v1.2.5, installed in dev environment)
- RFC 6986 Example 1 test vectors (M1 forward and reverse byte orderings verified)

## Root Cause (Suspected — not confirmed by step-through)

Three areas in `src/os/crypto/streebog.spl` (650 lines) are likely wrong:

### 1. `_g_N` key schedule — incorrect E(key, m) implementation (lines 492–509)

RFC 6986 §7.1 specifies the 12-round cipher E as:

```
K[0] = LPS(h XOR N)
state = m XOR K[0]
for i in 0..11:
    state = LPS(state) XOR K[i+1]
    K[i+1] = LPS(K[i]) XOR C[i]
```

The implementation sets `K = key` (no initial LPS), then `state = m XOR K`,
and the loop runs `state = LPS(state); K = LPS(K); K ^= C[i]; state ^= K`.
This misses the initial `LPS` application to K and misorders the round-key XOR
relative to the state LPS.

### 2. L-transform MDS matrix (lines 435–487)

The L-transform applies the MDS matrix from RFC 6986 §5.2.2 (64×64 over GF(2)).
The `_apply_l` function indexes coefficients as `c_idx = ((col - k) + 64) % 8`,
using `% 8` not `% 64`; this only cycles through 8 of the 64 possible positions.
The `_mds_row_coeff` function hardcodes 8 coefficients.  The RFC matrix uses a
circulant construction over 8 u64 words (with a specific polynomial), not per-row
8-byte circulant independently.  The GF multiplication polynomial also needs
verification against RFC §5.2.2 (`x^8 + x^7 + x^6 + x + 1 = 0x1C3`).

### 3. Output byte extraction (lines 626–632)

The state `h` after finalization is a list of 64 i64 byte-values.  The
extraction loop calls `h.get(j)` which is byte-at-index.  This appears correct
for a byte-array state.  However, if the state representation were ever changed
to 8 u64 words this would break.  Low suspicion — examine after fixing 1 and 2.

## Blocked Tests

- `test/unit/os/crypto/streebog_kat_spec.spl` — 3 of 5 assertions fail
- Any downstream code using `streebog_512` or `streebog_256` (HMAC-Streebog,
  KDF, TLS 1.3 GOST profile) is producing wrong digests.

## Fix Guidance

1. Rewrite `_g_N` to match RFC 6986 §7.1 precisely:
   - Apply `LPS` to `(h XOR N)` to produce K[0].
   - Compute initial state as `m XOR K[0]`.
   - Round loop: `state = LPS(state) XOR K[i+1]` where `K[i+1] = LPS(K[i]) XOR C[i]`.
2. Verify the L-transform (MDS) against the matrix in RFC 6986 §6.4; check that
   `_gf_mul_streebog` uses the correct reducing polynomial (`0x1C3`).
3. After each fix, run the KAT spec to observe incremental improvement.
4. The spec vectors at `test/unit/os/crypto/streebog_kat_spec.spl` are correct
   (the Streebog-512("") spec typo was fixed in commit alongside this bug doc).

## Related

- `test/unit/os/crypto/streebog_kat_spec.spl` — the KAT spec (spec-side typo
  for Streebog-512("") was fixed; remaining failures are all impl bugs)
- `src/os/crypto/streebog.spl` — implementation under investigation
- RFC 6986 §7.1, §6.4 — normative reference for E and L transforms
