# OS crypto modules call helpers under names they no longer define

Status: FIXED on Phase 1; not yet built natively. Severity: P1. Date: 2026-10-31.

## Symptom

Private helpers in `src/os/crypto` were renamed with a module prefix, but some call
sites kept the old name.

| File | Call | Before | After |
| --- | --- | --- | --- |
| `aes128_gcm.spl` | `_make_j0`, `_inc32` had no definition in reach | NIST spec 0/12 | 12/12 |
| `curve25519_smalllimb.spl` | `_cswap_pair` resolved to `curve25519.spl`'s `Fe25519` version and failed on `[u64]` limbs | RFC 7748 spec 2/10 | 10/10 |
| `curve25519_smalllimb.spl` | `_clamp_scalar` in a probe, now `_sl_clamp_scalar` | not isolated | probe spec 3/3 |
| `aes256_gcm.spl` | `_append_bytes` resolved to another module's function | NIST spec 12/12 | 12/12 |

Results are from the Phase 1 seed interpreter. A native build resolves names
differently, so these need a Phase 2 run too.

## Still open

`fe_cswap` in `curve25519_smalllimb.spl` branches on `if swap == 0`, and that bit comes
from the private scalar, so the X25519 ladder is not constant-time. This predates the
fix and was not changed.

## How it was found

A scan comparing each `src/os/crypto/*.spl` file's private calls with the definitions
in that file and its direct `os.crypto` imports. `rsa_pss.spl` was also flagged, but
`_PssTlv` is a class there, so that one is not a defect. The scan is not a gate.
