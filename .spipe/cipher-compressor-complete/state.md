# SStack State: cipher-compressor-complete

## User Request
> check cipher and compressor remains and complete

## Task Type
feature

## Refined Goal
> Port remaining SMF-only cipher (AES, RSA) and compression (gzip/deflate) modules to pure .spl, completing the crypto and compression standard library. AES: 7 files, RSA: 10 files, gzip: 8 files — total 25 SMF→SPL ports.

## Acceptance Criteria
- [ ] AC-1: AES core — sbox, types, utilities ported to .spl with pure-Simple lookup tables
- [ ] AC-2: AES cipher — key_expansion, cipher (encrypt/decrypt block), padding ported to .spl
- [ ] AC-3: AES modes — ECB, CBC, CTR mode wrappers ported to .spl
- [ ] AC-4: RSA math — modular arithmetic, primality testing, byte conversion ported to .spl
- [ ] AC-5: RSA operations — key_gen, encrypt, sign, padding (PKCS#1 v1.5, OAEP) ported to .spl
- [ ] AC-6: Gzip deflate — lz77, huffman, deflate, inflate ported to .spl
- [ ] AC-7: Gzip container — crc32, header, stream, compress ported to .spl
- [ ] AC-8: Existing crypto tests pass (SHA-256, SHA-512, HMAC, crypto_ref_harness, MIR cipher specs)
- [ ] AC-9: New specs verify AES encrypt/decrypt round-trip, RSA sign/verify, gzip compress/decompress

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Task type: feature — SMF→SPL port of 25 cipher/compression modules.

Existing live .spl: SHA-256, SHA-512, HMAC, constant_time, types (crypto); compress mod/init/upx, gzip types (compression).
SMF-only (need port): AES (7), RSA (10), gzip (8) = 25 files.

Parallel agent plan — 3 workstreams:
- WS-A (AES): 7 files in src/lib/common/aes/
- WS-B (RSA): 10 files in src/lib/common/rsa/ (NOTE: depends on existing crypto utils)
- WS-C (Gzip): 8 files in src/lib/nogc_sync_mut/compression/gzip/

All workstreams have disjoint file scopes. WS-A and WS-B are independent. WS-C is independent.
