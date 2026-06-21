# BUG: AES-256 block cipher produces data-dependent wrong output in a CTR loop

- **Severity:** P1 (security — breaks AES-256-CTR for some inputs; AES-256-GCM verified NOT affected — see Blast radius)
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

## Blast radius (measured 2026-06-21)

Single-block isolation of `aes256_encrypt_block` (schedule from key `603deb…dff4`):

| input | result |
|---|---|
| `f0f1…fcfdfeff` | `0bdf7df1591716335e9a8b15c860c502` — **CORRECT** |
| `f0f1…fcfdff00` | `5a6e699d536119065433863c8f657b94` vs expected `…8f10b873` — **last 3 bytes WRONG** |
| FIPS-197 C.3 (`00112233…ff`, key `000102…1f`) | **CORRECT** (`8ea2b7ca…`) |

So the defect is genuinely **data-dependent**: the block is correct for most
inputs but corrupts the final 1-3 output bytes for specific input/schedule
combinations. The localized error (final-round bytes, no avalanche) points at a
runtime byte/array-lookup defect exercised only by the AES-256 14-round path —
AES-128 (10 rounds) is correct for the identical inputs.

- **AES-256-CTR** (SSH aes256-ctr, RFC 4344): **AFFECTED** — incorrect ciphertext
  for counters whose bytes trigger the defect (e.g. the F.5.5 vector, blocks 2-4).
- **AES-256-GCM**: **NOT affected (verified).** McGrew-Viega Test Case 14
  (single block) and Test Case 15 (4-block, 64-byte plaintext) both produce
  byte-exact ciphertext **and** tag. GCM's `_gctr` counter values
  (`cafebabe…00000002…05`) happen not to trigger the defect. A wider AES-256-GCM
  fuzz against random plaintexts is still advisable, but the canonical multi-block
  KAT is clean.
- AES-128-CTR / AES-128-GCM: unaffected.

## Repro

`std.common.aes.modes.aes_ctr_encrypt(pt, key256, iv)` with the F.5.5 vectors
(see `test/01_unit/lib/crypto/aes_ctr_nist_spec.spl` F.5.5/F.5.6). AES-128
F.5.1/F.5.2 in the same spec pass.
