# Bug: `quic_aead_encrypt` (binary AES-128-GCM) fails in interpreter, SEGFAULTs under JIT

- **ID:** quic_aead_encrypt_fails_interp_segfaults_jit_2026-06-16
- **Severity:** P1 (RED spec + native crash; contradicts prior "KAT verified" closeout)
- **Status:** OPEN
- **Area:** std.io.quic.quic_crypto / std.common.crypto.aes_gcm / JIT codegen

## Symptom
`test/01_unit/lib/nogc_async_mut/quic/quic_aead_spec.spl` is **RED** — 2 of 3 `it`
blocks pass, the encrypt KAT fails:
- `it "encrypts to the OpenSSL-verified ciphertext+tag"` →
  `expect(_enc()).to_equal("d6b38a7873b8d79ee6855b9ddc6d15e663365f87")` FAILS.
- Round-trip decrypt and tampered-reject pass.

Under `bin/simple run` (JIT/native), the same `quic_aead_encrypt(...)` call
**segfaults** (rc=139, core dumped) immediately after entry — prints `START`,
then crashes inside the encrypt call.

This contradicts an earlier session closeout that reported quic_aead_spec as
"KAT verified vs OpenSSL, green". The header-protection spec (sibling) is genuinely
green (6/0); only the AEAD encrypt path is broken.

## Repro
Interpreter (assertion fail):
```
export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed
bin/simple test test/01_unit/lib/nogc_async_mut/quic/quic_aead_spec.spl   # 1 failed
```
JIT (segfault) — minimal probe:
```
# main(): quic_aead_encrypt(keys, 2, header22B, payload4B) with RFC9001 §A.2 key/iv
bin/simple run <probe>.spl        # prints START then SIGSEGV (rc=139)
```
Inputs (RFC 9001 §A.2 Client Initial): key `1f369613dd76d5467730efcbe3b1a22d`,
iv `fa044b2f42a3fd3b46fb255c`, pn=2 (nonce = iv XOR pn → …255e), header = 22-byte
Initial header, payload `01020304`, AAD = header.

## Suspected cause
The session wired `quic_aead_encrypt/decrypt` from hex externs to binary
`std.common.crypto.aes_gcm.{aes128_gcm_encrypt,aes128_gcm_decrypt}` plus an
`[i64]→[u8]` key/nonce bridge and a `ct||tag` split. Decrypt round-trips, so key
expansion + GHASH are largely correct; the encrypt-only divergence + JIT segfault
points at the encrypt return-path / ct||tag concatenation or the `[i64]/[u8]`
bridge buffer (likely an OOB or NULL deref the interpreter masks but cranelift
faults on — cf. the AAD/tag-length class in `aes_gcm_pure_empty_aad_tag_mismatch`).

## Next
- Diff `_enc()` output vs expected byte-by-byte under the interpreter (capture the
  actual hex) to localize encrypt vs tag.
- Run under a debugger / `SIMPLE_*` backtrace to get the JIT segfault frame.
- The QUIC AEAD wiring should NOT be considered landed-green until this is fixed;
  prior memory/lane notes overstated it.
