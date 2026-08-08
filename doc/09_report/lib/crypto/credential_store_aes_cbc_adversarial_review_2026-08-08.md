# Adversarial crypto review — `23839a41331` (credential store AES-CBC)

Date: 2026-08-08. Scope: commit `23839a41331` "fix(security): real AES-CBC +
PKCS#7 and a CSPRNG IV for the credential store". Reviewer ran every vector
below independently against the code **as landed**; the landed spec was not
trusted as evidence.

Engine caveat: all runs are on `bin/simple` (Rust bootstrap seed, interpreter
path, `SIMPLE_EXECUTION_MODE=interpret`). GREEN here does **not** prove
JIT/native behaviour, where the known `Dict.len()`/`.get()` and slice traps
live. The AES code touches neither dicts nor text slicing on secret data, so
the exposure is judged low, but it is unproven.

Harness: `build/kat_review/aes_kat_review.spl`, `build/kat_review/store_review.spl`
(scratch, not committed).

## Vectors actually run

```
PASS C.1 gcm enc            69c4e0d86a7b0430d8cdb78070b4c55a
PASS C.1 gcm DEC            00112233445566778899aabbccddeeff
PASS C.1 cipher.spl enc     69c4e0d86a7b0430d8cdb78070b4c55a
PASS C.1 cipher.spl DEC     00112233445566778899aabbccddeeff
PASS C.3 gcm enc            8ea2b7ca516745bfeafc49904b496089
PASS C.3 gcm DEC            00112233445566778899aabbccddeeff
PASS C.3 cipher.spl enc     8ea2b7ca516745bfeafc49904b496089
PASS C.3 cipher.spl DEC     00112233445566778899aabbccddeeff
PASS F.2.1 CBC-128 enc (leading 64B)
     7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b2
     73bed6b8e3c1743b7116e69e222295163ff1caa1681fac09120eca307586e1a7
     (total output 80B = 64 + one full PKCS#7 block; pad block
      8cb82807230e1321d3fae00d18cc2012)
PASS F.2.5 CBC-256 enc (leading 64B)
     f58c4c04d6e5f1ba779eabfb5f7bfbd69cfc4e967edb808d679f777bc6702c7d
     39f23369a9d9bacfa530e26304231461b2eb05e2c39be9fcda6c19078c6a9d1b
PASS F.2.2 CBC-128 dec — F.2.2 ciphertext chained manually through
     aes128_decrypt_block + XOR with the PREVIOUS CIPHERTEXT block recovers the
     published plaintext 6bc1bee2...e66c3710
PASS CBC-256 round-trip through the landed aes_cbc_decrypt
PASS wrong-key v2 decrypt returns nil (fail-closed)
PASS invalid-padding ciphertext returns nil (fail-closed)
PASS IV freshness — same plaintext, same key, two calls:
     encrypted:v2:f77f946a1d85ea7ee40fb1a27ed07c2b...
     encrypted:v2:dffa5c9e7f4a92c635a0fad75ce08c18...
PASS synthetic v1 record (encrypted:<hex_iv><hex_ctr_ct>) decrypts to
     'legacy_secret'; v2 record under a wrong key returns '' not garbage
```

Landed spec re-run: `SPEC FILE VERDICT: test/01_unit/lib/crypto/aes_cbc_fips197_nist_spec.spl
declared>=18 executed=18 passed=18 failed=0 dropped=0`.

## Five explicit verdicts

1. **Does the landed CBC interoperate with standard AES-CBC?** **YES**, proven
   by published vectors, not round-trip. F.2.1 and F.2.5 leading-64-byte output
   matches SP 800-38A exactly; the 80-byte total is correct RFC 5652 behaviour
   (aligned input gains a full pad block), not a defect. Chaining direction is
   correct in both directions: `modes.spl:180` XORs `prev` (IV, then previous
   *ciphertext*) into the plaintext before encryption; `modes.spl:227-229` XORs
   the previous *ciphertext* block after the inverse cipher (`prev = block`,
   where `block` is ciphertext). **The landed spec COULD have caught an inverted
   chaining bug** — contrary to an initial concern, it does contain the real
   F.2.1/F.2.5 expected ciphertexts (as byte lists, `_cbc_ct128`/`_cbc_ct256`,
   spec:134-160) and compares the leading 64 bytes. No coverage gap here.
2. **Is the IV genuinely CSPRNG and fail-closed?** **YES.** `store.spl:263`
   calls `rt_random_hex(16)`, which resolves to
   `interpreter_extern/random.rs:109-126` → `rand::rngs::OsRng.try_fill_bytes`,
   returning `Value::Nil` on error. `store.spl:264-271` fails closed on nil, on a
   short hex string, and on a short decoded IV — no weak fallback exists on any
   path. IV is a full 16 bytes, stored as the first 32 hex chars of the payload,
   never derived from the plaintext. Empirically distinct across encryptions.
3. **Is PKCS#7 correct including the full-block case and fail-closed on unpad?**
   **YES for the new code.** `_pkcs7_pad_16` (`modes.spl:111-123`) uses
   `16 - (n % 16)`, which yields 16 for aligned input — verified: 64B in → 80B
   out. `_pkcs7_unpad_16` (`modes.spl:131-149`) rejects empty/unaligned input,
   `pad_len` outside 1..16, and any pad byte that is not equal to `pad_len`.
   **The pre-existing `src/lib/common/aes/padding.spl:33` `pkcs7_unpad` is still
   FAIL-OPEN** — verified empirically: `pkcs7_unpad([0x99 × 16])` returns all 16
   bytes unchanged. The new path does not call it; other callers still do.
4. **Is the migration safe?** **YES for read compatibility; see finding F5 for
   the durability gap.** The v1 format was verified against the parent commit
   (`23839a41331^:.../store.spl`), which wrote
   `"encrypted:" + bytes_to_hex(iv) + bytes_to_hex(ct)` — the IV **was** stored,
   so the new `payload[0..32]` slice is layout-correct. The version test is
   unambiguous: `starts_with("v2:")` on a payload that in v1 is pure lowercase
   hex, and neither `v` nor `:` is a hex character. Misparse in either direction
   is impossible. A failed decrypt returns `""`, never crashes and never writes.
   No path in `store.spl` destroys a credential file.
5. **Which inverse-cipher implementation passes KAT?** **BOTH.**
   `crypto/aes_gcm.spl` (`aes128_decrypt_block:541`, `aes256_decrypt_block:545`)
   and the pre-existing `aes/cipher.spl` (`aes_decrypt_block:428`) each pass
   FIPS-197 C.1 and C.3 in the decrypt direction. Correctness does not decide the
   dedup direction. What does: **the two use incompatible representations** —
   `aes_gcm.spl` takes `[u8]` state and a forward round schedule consumed in
   reverse round order; `cipher.spl` takes `list` (`[i64]`) and its own
   `expand_key` output, and has a SIMD path. Dedup is therefore an adapter/rewrite,
   not a drop-in swap. `cipher.spl` is the better keep target (SIMD + native
   `rt_aes_decrypt_block_with_expanded`), but `modes.spl` would need a
   `[u8]`↔`[i64]` shim.

## Findings, most severe first

| # | Location | Finding | Severity | Introduced by this commit? | Confidence |
|---|----------|---------|----------|---------------------------|-----------|
| F1 | `store.spl:150-186` | `credential_key_generate` builds only **24** key bytes (3 bcrypt blocks × 8) but pads to `AES_KEY_SIZE = 32` with **literal 0x00**. Every derived AES-256 key ends in 8 zero bytes on every install. Effective strength ≤192 bits, and the last 8 bytes are publicly known. Not break-now, but it is not the AES-256 the code claims. | MEDIUM | No — pre-existing | High (by inspection; the loop pushes 8 bytes per block for 3 blocks, then `else: aes_key.push(0)` for i=24..31) |
| F2 | `store.spl:64-66` (`KDF_SALT`) | Hardcoded fixed KDF salt, acknowledged in a comment ("In production, this should be randomly generated"). The same passphrase yields the identical AES key on every machine, so one precomputed table attacks every install. | MEDIUM | No — pre-existing | High |
| F3 | `store.spl:196` | `rt_file_write_text(path, key_hex)` writes the master key with **no `chmod`**. No permission handling exists in the runtime extern either. Under this machine's `umask 0002` the key file lands **0664 — group-readable**. Any local user in the group reads every stored credential. | MEDIUM | No — pre-existing | High (no chmod call exists anywhere on the path) |
| F4 | `aes/padding.spl:33-52` | `pkcs7_unpad` **fails open**: on invalid padding it returns its input unchanged, handing pad bytes back as plaintext. Verified: `[0x99 × 16]` → 16 bytes unchanged. Any caller using it as a decrypt trailer check is a padding-oracle enabler. The commit correctly avoided it, but did not fix it. | MEDIUM | No — pre-existing; another lane may own it | High (empirical) |
| F5 | `store.spl:342-347` | **No upgrade-on-read/write.** A v1 record decrypts correctly forever but is never re-encrypted to v2, so legacy secrets linger under CTR-with-plaintext-derived-IV (the original XOR-leak defect) until some caller happens to rewrite them. No enumeration/migration routine exists. | LOW-MEDIUM | Yes (the migration design) | High |
| F6 | `store.spl:196` | `credential_key_generate` is declared `-> bool` but its last expression is the result of `rt_file_write_text`; `rt_ensure_dir`'s result is discarded. A failed key write can be reported as success depending on the extern's return. | LOW | No | Medium |
| F7 | `modes.spl:140-142` | `_pkcs7_unpad_16` short-circuits on the first mismatching pad byte, so unpad time leaks the pad-prefix length. For a local credential file with no remote decryption oracle this is not exploitable; noted for completeness rather than action. | INFO | Yes | High |

Nothing in the CBC/PKCS#7/IV core of this commit is defective. F1–F4 are
pre-existing weaknesses in the surrounding key management that the commit did not
introduce and did not claim to fix; they are the remaining real risk in this
module and should be filed separately.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
