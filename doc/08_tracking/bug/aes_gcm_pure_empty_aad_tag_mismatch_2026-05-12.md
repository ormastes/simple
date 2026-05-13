# AES-GCM Pure Empty-AAD Tag Mismatch

Date: 2026-05-12
Status: Open

`test/unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl` is a known blocker for the cipher/compression algorithm gate. The pure `os.crypto.aes_gcm` path computes a wrong tag for the AES-256-GCM CAVS V3 vector with empty AAD and 16-byte plaintext.

Current gate handling: strict mode must fail on this spec; `CIPHER_COMPRESS_ALLOW_KNOWN_FAIL=1` may skip it while unrelated algorithm work is verified.

Next step: isolate AES block output, GHASH input, J0 construction, and first-counter encryption against the vector before changing tag assembly.
