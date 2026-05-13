# Plan: All Cipher and Compression Algorithm Gate
 
 ## Status: 2026-05-13 CURRENT
 
 Goal: extend the existing C/Rust/Simple algorithm parity workflow from XXHash64 and ChaCha20 to the full in-repo cipher, crypto, and compression surface. The gate should prove correctness first, then performance where an apples-to-apples reference exists.

Performance comparison rule: every cipher, checksum, hash, KDF, public-key, and
compression row must eventually report `Simple/C` and `Simple/Rust` ratios.
Values above `1.00x` mean Simple is faster than that baseline. Rows without a
C/Rust/Simple parity benchmark stay `TBD, target >1.00x`; they do not count as
complete or faster-than-baseline evidence.
 
 ## Scope
 
 Cipher/crypto families already present in the repo:
 
 - Block ciphers and modes: AES-GCM, AES-CCM, AES-XTS, AES-CMAC, AES-GCM-SIV, Camellia, ARIA, SEED, Serpent, Twofish, SM4, TEA, RC4.
 - Stream ciphers: ChaCha20, Salsa20, XSalsa20, ZUC, SNOW3G.
 - AEAD/MAC/KDF: Poly1305, ChaCha20-Poly1305, OCB3, HMAC, HKDF, PBKDF2, scrypt, Argon2.
 - Hash/checksum: SHA-1/2/3, BLAKE2, BLAKE3, RIPEMD160, Whirlpool, Streebog, Tiger, SM3, CRC32, Adler32, XXHash, SipHash, KMAC/cSHAKE.
 - Public-key/post-quantum: RSA/PSS/PKCS#1, ECDSA/ECDH P-256/P-384/P-521, Curve25519/448, Ed25519/448, FFDHE, ML-KEM, ML-DSA, SLH-DSA.
 
 Compression families already present in the repo:
 
 - Deflate/Gzip/zlib and PNG inflate.
 - LZ4 and frame/block handling.
 - Snappy.
 - Zstd frame, literals, FSE, HUF, sequences, dictionaries.
 - LZMA2/XZ.
 - Brotli.
 - Shared Huffman and LZ77 helpers.
 - Kernel/loader Zstd decompression.
 - HTTP/WebSocket compression wrappers.
 
 ## Gate Tiers
 
 ### Tier 0: Inventory
 
 Command:
 
 ```bash
 test/perf/port_algorithms/run_cipher_compress_gate.shs --list
 ```
 
 Stop condition:
 
 - The runner prints the crypto/compression spec sets it would execute.
 - No source or test is silently omitted from the generated `all` mode inventory.
 
 ### Tier 1: Core Correctness
 
 Command:
 
 ```bash
 test/perf/port_algorithms/run_cipher_compress_gate.shs
 ```
 
 Stop condition:
 
 - Core crypto and compression specs pass in interpreter mode.
 - Existing XXHash64/ChaCha20 C/Rust/Simple benchmark parity still passes.
 - Any failure is classified as a specific bug document or a named follow-up, not a vague "crypto failed" bucket.
 
Current result on 2026-05-13: strict Tier 1 is not yet green. The runner and
classification path are in place, and known blockers can be skipped explicitly:
 
 ```bash
 CIPHER_COMPRESS_ALLOW_KNOWN_FAIL=1 test/perf/port_algorithms/run_cipher_compress_gate.shs
 ```
 
2026-05-12 compiler/interpreter optimization update:

- Proven `[u32]` array reads/writes now have MIR fast paths through
  `rt_typed_words_u32_at` and `rt_typed_words_u32_set`, matching the existing typed `[u8]`
  strategy and avoiding generic `rt_index_get` / `rt_index_set` dispatch in
  ChaCha-style word-state loops.
- Regression tests lock the new lowering:
  `cargo test -p simple-compiler u32_index_set_uses_word_fast_path` and
  `cargo test -p simple-compiler u32_array_index_uses_word_fast_path`.
- The current stop condition is still correctness first. AES-GCM V3 remains a
  known blocker: GHASH passes with known-good H/CT, but AES-256 block canaries
  fail for H, J0, and first counter.

2026-05-13 algorithm correctness update:

- Fixed the OS Poly1305 tag serializer in `src/os/crypto/poly1305.spl`; `_put_le_u32` now returns the appended buffer and `poly1305_finalize` assigns each append.
- Verified `test/unit/lib/crypto/poly1305_rfc8439_spec.spl`, `test/unit/os/crypto/chacha20_poly1305_spec.spl`, and `test/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.spl` all pass in interpreter mode with `--no-cache`.
- Restored the documented `test/perf/port_algorithms/run_cipher_compress_gate.shs` runner. Core mode now passes 10 specs and skips the 3 named blockers when `CIPHER_COMPRESS_ALLOW_KNOWN_FAIL=1` is set.
- Added the compiler/runtime `[u32]` typed-word lowering in the Rust compiler path without changing algorithm sources. MIR now emits word get/set calls for typed `[u32]` arrays, Cranelift inlines them into direct slot load/store with bounds checks, and runtime/interpreter symbol plumbing preserves fallback behavior.
- Verified the rebuilt compiler with the port algorithm benchmark: checksum parity passed for XXHash64, CRC32, Adler32, and ChaCha20. Core algorithm gate still passes with documented blockers skipped: `passed=10 skipped=3 failed=0`.

### Tier 2: Full In-Repo Correctness
 
 Command:
 
 ```bash
 CIPHER_COMPRESS_SCOPE=all test/perf/port_algorithms/run_cipher_compress_gate.shs
 ```
 
 Stop condition:
 
 - All discovered `test/unit/**/{crypto,compress,compression,huffman,lz77}*spec.spl` tests pass, excluding only explicitly documented pre-existing bugs.
 - The exclusion list must be in this plan or in `doc/08_tracking/bug/`.
 
 ### Tier 3: Cross-Language Performance
 
 Command:
 
 ```bash
 SIMPLE_LLVM_PROBE=1 SIMPLE_DISASM_PROBE=1 test/perf/port_algorithms/run_port_algorithm_benchmarks.shs
 ```
 
 Stop condition:
 
 - Correctness parity passes before any speed number counts.
 - C, Rust, Simple default, and Simple LLVM rows exist for each benchmarked algorithm.
 - New algorithms use dependency-free C/Rust references first. External OpenSSL/zlib/libzstd comparisons are optional separate lanes.
 - Simple default and Simple LLVM each exceed both portable C and portable Rust throughput (`Simple/C > 1.00x` and `Simple/Rust > 1.00x`) before an algorithm is marked complete for the optimization-plugin goal. Interim engineering gates may still record 70% Rust / 50% C progress, but those rows remain incomplete until they are faster than both baselines.

Latest measured median ratios from the source-built 2026-05-13 Cranelift sample:
MB/s columns are independent per-implementation medians. `Simple/C` and
`Simple/Rust` are medians of the per-run ratio output, so they may differ from a
direct division of the median MB/s columns on noisy samples.

| Family | Algorithm | C median MB/s | Rust median MB/s | Simple median MB/s | Simple/C | Simple/Rust | Status |
|--------|-----------|---------------|------------------|--------------------|----------|-------------|--------|
| Non-crypto hash | XXHash64 | 8594 | 7884 | 8594 | 0.93x | 1.04x | Faster than Rust, still below C |
| Checksum | CRC32 | 311 | 337 | 280 | 0.83x | 0.85x | Below C/Rust |
| Checksum | Adler-32 | 2532 | 2610 | 2329 | 0.93x | 0.90x | Below C/Rust after reducer lowering |
| Stream cipher | ChaCha20 | 314 | 347 | 364 | 1.15x | 1.05x | Faster than C/Rust |

### Remaining Performance Matrix

This matrix is the plan-of-record for the unfinished rows. `TBD` means no
apples-to-apples C/Rust/Simple parity benchmark is accepted yet. A row is not
complete until correctness passes and both ratio columns are above `1.00x`.

| Family | Algorithms | Simple/C | Simple/Rust | Remaining compiler/plugin work |
|--------|------------|----------|-------------|--------------------------------|
| Non-crypto hash | XXHash64 | 0.93x | 1.04x | General MIR CSE/GVN for repeated rotates, shifts, adds, xors, and multiply-derived addressing |
| Checksum | CRC32 | 0.83x | 0.85x | Static table materialization, table lookup hoisting, typed byte slice lookup facts |
| Checksum | Adler-32 | 0.93x | 0.90x | Weighted byte-reduction plugin, chunked modulo deferral, range/bounds proof |
| Stream cipher | ChaCha20 | 1.15x | 1.05x | Keep as canary; prevent regressions while generalizing typed word-state lowering |
| Block cipher/mode | AES-GCM, AES-CCM, AES-XTS, AES-CMAC, AES-GCM-SIV | TBD, target >1.00x | TBD, target >1.00x | Static S-box/T-table handling, GHASH multiply lowering, block-state stack storage |
| Block cipher | Camellia, ARIA, SEED, Serpent, Twofish, SM4, TEA | TBD, target >1.00x | TBD, target >1.00x | Rotate/table/bit-slice recognition, no-box word arrays, inlining cost model |
| Stream cipher | Salsa20, XSalsa20, ZUC, SNOW3G, RC4 | TBD, target >1.00x | TBD, target >1.00x | Word-state typed arrays, rotate idiom lowering, byte-stream output fusion |
| AEAD/MAC | Poly1305, ChaCha20-Poly1305, OCB3, HMAC, KMAC/cSHAKE | TBD, target >1.00x | TBD, target >1.00x | Wide multiply/reduction facts, block iterator fusion, fixed-size buffer lowering |
| KDF/password | HKDF, PBKDF2, scrypt, Argon2 | TBD, target >1.00x | TBD, target >1.00x | Loop-invariant allocation removal, typed scratch buffers, memory-fill/copy intrinsics |
| Hash | SHA-1/2/3, BLAKE2, BLAKE3, RIPEMD160, Whirlpool, Streebog, Tiger, SM3, SipHash | TBD, target >1.00x | TBD, target >1.00x | Rotate/message-schedule CSE, static IV materialization, unrolled block lowering |
| Public-key/PQ | RSA/PSS/PKCS#1, ECDSA/ECDH, Curve25519/448, Ed25519/448, FFDHE, ML-KEM, ML-DSA, SLH-DSA | TBD, target >1.00x | TBD, target >1.00x | Big-int limb specialization, constant-time select lowering, fixed-array stack storage |
| Compression | Deflate, Gzip, zlib, PNG inflate, LZ4, Snappy, Zstd, LZMA2/XZ, Brotli, Huffman, LZ77 | TBD, target >1.00x | TBD, target >1.00x | Bitstream batch reads, table hoisting, match-copy fusion, static Huffman/FSE tables |
| Loader/wrappers | Kernel Zstd, HTTP/WebSocket compression | TBD, target >1.00x | TBD, target >1.00x | Facade import fix, streaming buffer specialization, native fallback guard |
 
 ## First Expansion Order
 
 1. Keep XXHash64 and ChaCha20 as the baseline canaries.
 2. Add checksum/hash canaries: CRC32, Adler32, SHA-256, BLAKE2s/BLAKE2b.
 3. Add cipher canaries: AES block/mode KATs, ChaCha20-Poly1305, Salsa20/XSalsa20.
 4. Add compression canaries: Deflate, Gzip, LZ4, Snappy, Zstd frame/HUF/FSE.
 5. Add broad full-suite mode and classify pre-existing failures.
 6. Add C/Rust performance references only after Tier 1 correctness stays stable.
 
 ## Current Hardening Notes
 
 - Keep dependency-free references in `test/perf/port_algorithms` so the gate runs on a fresh developer machine.
 - Do not benchmark algorithms whose reference implementation imports broken SIMD/native symbols until the import/runtime-symbol issue is fixed or explicitly bypassed.
 - Do not count speed if native compile falls back to interpreter.
 - Keep compiler/runtime optimizations separate from algorithm rewrites unless the rewrite exposes a real lowering fact such as typed byte access, length facts, or direct word loads/stores.
 
## 2026-05-12 Implementation Notes

- Added `test/perf/port_algorithms/run_cipher_compress_gate.shs`.
- Added `core` and `all` inventory modes.
- Added explicit `CIPHER_COMPRESS_ALLOW_KNOWN_FAIL=1` handling for documented blockers.
- Added `CIPHER_COMPRESS_CONTINUE_ON_FAIL=1` for discovery runs that should collect more than the first failure.
- Verified the post-AES compression/checksum core set passes through Snappy, then exposed the Zstd large-payload timeout.

## 2026-05-13 Compiler Optimization Notes

- Added typed `[u8]` and `[u32]` push lowering in the Rust compiler path so common byte-buffer and word-state builders avoid generic `rt_array_push` boxing.
- Runtime, interpreter-extern, native symbol, and ELF resolution plumbing now expose `rt_typed_bytes_u8_push` and `rt_typed_words_u32_push`.
- The change is shared compiler/runtime infrastructure for all algorithms; no crypto or compression algorithm source was rewritten.
- Verification: targeted MIR/runtime tests, package checks, release driver build, checksum parity for the port benchmark, and cipher/compress gate `passed=10 skipped=3 failed=0`.
 
## Known Blockers
 
 - `test/unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl`: pure `os.crypto.aes_gcm` computes the wrong tag for AES-256-GCM CAVS V3 with empty AAD and 16-byte plaintext. Bug: `doc/08_tracking/bug/aes_gcm_pure_empty_aad_tag_mismatch_2026-05-12.md`.
 - `test/unit/lib/common/zstd_frame_variants_spec.spl`: large 70,000-byte single-segment payload example times out in interpreter mode. Bug: `doc/08_tracking/bug/zstd_frame_variants_large_payload_timeout_2026-05-12.md`.
 - `test/unit/os/kernel/loader/zstd_decompress_spec.spl`: compression facade helpers do not resolve through `std.common.compress.{...}` in the current checkout. Bug: `doc/08_tracking/bug/kernel_zstd_adapter_compress_facade_import_2026-05-12.md`.
