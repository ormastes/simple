# AES-XTS IEEE 1619 KAT mismatch after parser cleanup

Date: 2026-05-27
Status: Open
Severity: High — AES-XTS vectors execute but 14/15 fail

## Symptom

After removing parser blockers in `src/os/crypto/aes_xts.spl`, the IEEE 1619
KAT spec runs in interpreter mode but still fails most vectors:

```bash
bin/simple test test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl --mode=interpreter --clean --timeout 160
```

Observed result: 1 passed, 14 failed, runtime about 91 seconds.

## Current Status

This is no longer blocked by the earlier AES extern byte-array rejection or by
semicolon-separated table initializers. The remaining issue is algorithmic or
test-vector handling in the AES-XTS implementation path.

## Next Diagnostic

Run the spec through `bin/simple run` to capture per-vector mismatches, then
narrow whether the failure is in AES-256 key expansion, inverse AES, tweak
doubling, or ciphertext stealing.
