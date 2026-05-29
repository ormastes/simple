# AES-XTS IEEE 1619 KAT mismatch after parser cleanup

Date: 2026-05-27
Status: Resolved 2026-05-27
Severity: High — AES-XTS vectors executed but initially failed 14/15

## Symptom

After removing parser blockers in `src/os/crypto/aes_xts.spl`, the IEEE 1619
KAT spec runs in interpreter mode but still fails most vectors:

```bash
bin/simple test test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl --mode=interpreter --clean --timeout 160
```

Initial observed result after parser cleanup: 1 passed, 14 failed, runtime about
91 seconds.

## Resolution

Two AES-XTS implementation bugs were fixed:

- AES-128 XTS passed raw key bytes into `aes128_encrypt_block`, but that
  function expects expanded round keys. XTS now expands the AES-128 data and
  tweak keys before AES block encryption.
- AES-256 XTS decrypt used a local duplicate key expansion with drift from the
  canonical AES-256 schedule. XTS now uses `aes256_gcm.aes256_key_expansion`
  for AES-256 decrypt.

Verification:

```bash
bin/simple check src/os/crypto/aes_xts.spl test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl
bin/simple test test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl --mode=interpreter --clean --timeout 180
```

The KAT now passes 15/15.
