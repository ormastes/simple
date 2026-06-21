# BUG: AES-256 block cipher produces data-dependent wrong output in a CTR loop

- **Severity:** P1 (security — affects AES-256-CTR and AES-256-GCM correctness)
- **Component:** `src/lib/common/crypto/aes_gcm.spl` (`aes256_encrypt_block` / `_aes_encrypt_block`) and/or the runtime that executes it (interpreter AND JIT)
- **Found:** 2026-06-21, while implementing `std.common.aes.modes` (AES-CTR).

## Symptom

AES-256-CTR (NIST SP 800-38A F.5.5) over the standard 64-byte plaintext with
key `603deb…dff4` and IV `f0f1…feff` produces:

```
block1  601ec313775789a5b7a7f504bbf3d228   CORRECT
block2  f443e3ca4d62b59aca84e990 cacaf5c5   first 12 bytes CORRECT, last 4 WRONG (expect cabf3622)
block3  2b0930daa23de94ce87017ba2d84988d   WRONG (expect 95b84d1b96c690ff2f2de30bf2ec89e0)
block4  dfc9c58db67aada613c2dd08457941a6   WRONG (expect 0253786e126504f821d448577949bf8b)
```

## What is NOT the cause (verified)

- **AES-CTR mode logic is correct** — the identical code path produces the
  EXACT NIST AES-128 F.5.1/F.5.2 vectors (all 4 blocks) and round-trips.
- **Counter increment is correct** — AES-128 uses the same counters
  (`…feff, …ff00, …ff01, …ff02`) and is byte-exact.
- **The AES-256 block cipher is correct standalone** — `aes256_encrypt_block`
  on FIPS-197 C.3 (`00112233…ff`, key `000102…1f`) returns the exact
  `8ea2b7ca516745bfeafc49904b496089`, and repeated calls are consistent
  (no schedule mutation).
- **Not JIT-specific** — reproduces identically under `bin/simple run` (JIT)
  and `bin/simple run <f> --interpret`.

## Conclusion

`aes256_encrypt_block` is correct for the FIPS-197 C.3 input but returns wrong
output (partial in block2, full in block3/4) for the F.5.5 counter inputs with
the F.5.5 key — i.e. a **data-dependent miscomputation** in the AES-256 path
that AES-128 (10 rounds) does not hit. The localized "last 4 output bytes"
error in block2 points at the final round / last state column. Since
`_aes_encrypt_block` is shared with the correct AES-128 path, the defect is most
likely in a low-level u8/array operation as exercised by the AES-256 round count
(14) for specific data — consistent with this repo's documented codegen/runtime
byte-arithmetic bugs.

## Impact

- **AES-256-CTR** (SSH aes256-ctr, RFC 4344) produces incorrect ciphertext.
- **AES-256-GCM** uses the same `aes256_encrypt_block` in a counter loop and is
  very likely affected for multi-block messages — this should be checked with a
  multi-block AES-256-GCM KAT.

AES-128-CTR / AES-128-GCM are unaffected.

## Repro

`std.common.aes.modes.aes_ctr_encrypt(pt, key256, iv)` with the F.5.5 vectors
(see `test/01_unit/lib/crypto/aes_ctr_nist_spec.spl` F.5.5/F.5.6). AES-128
F.5.1/F.5.2 in the same spec pass.
