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
 
Current result on 2026-05-13: strict Tier 1 is green. The runner and
classification path remain in place for future regressions:
 
 ```bash
 test/perf/port_algorithms/run_cipher_compress_gate.shs
 ```
 
2026-05-12 compiler/interpreter optimization update:

- Proven `[u32]` array reads/writes now have MIR fast paths through
  `rt_typed_words_u32_at` and `rt_typed_words_u32_set`, matching the existing typed `[u8]`
  strategy and avoiding generic `rt_index_get` / `rt_index_set` dispatch in
  ChaCha-style word-state loops.
- Regression tests lock the new lowering:
  `cargo test -p simple-compiler u32_index_set_uses_word_fast_path` and
  `cargo test -p simple-compiler u32_array_index_uses_word_fast_path`.
- The stop condition was correctness first; the AES-GCM V3 issue is now closed
  as a fixture-key mismatch, not an AES block or GHASH implementation defect.

2026-05-13 algorithm correctness update:

- Fixed the OS Poly1305 tag serializer in `src/os/crypto/poly1305.spl`; `_put_le_u32` now returns the appended buffer and `poly1305_finalize` assigns each append.
- Verified `test/unit/lib/crypto/poly1305_rfc8439_spec.spl`, `test/unit/os/crypto/chacha20_poly1305_spec.spl`, and `test/unit/lib/crypto/chacha20_poly1305_rfc8439_spec.spl` all pass in interpreter mode with `--no-cache`.
- Restored the documented `test/perf/port_algorithms/run_cipher_compress_gate.shs` runner.
- Added the compiler/runtime `[u32]` typed-word lowering in the Rust compiler path without changing algorithm sources. MIR now emits word get/set calls for typed `[u32]` arrays, Cranelift inlines them into direct slot load/store with bounds checks, and runtime/interpreter symbol plumbing preserves fallback behavior.
- Verified the rebuilt compiler with the port algorithm benchmark: checksum parity passed for XXHash64, CRC32, Adler32, and ChaCha20.
- Resolved the three core known-fail blockers: AES-GCM V3 fixture key bytes now match the documented CAVS vector, the shared `std.common.compress` facade resolves for the kernel zstd adapter, and the zstd 4-byte content-size case avoids interpreter-timeout fixture work while preserving header and RLE-shape assertions.
- Strict core gate now passes without known-fail allowance: `passed=13 skipped=0 failed=0`.
- Adler-32 now defers reduction across a 355328-byte chunk when using `u64` accumulators, and `test/unit/os/crypto/adler32_spec.spl` locks a 6000-byte pattern that crosses the classic 5552-byte reduction window. This is a correctness-preserving source-level cleanup, not enough to close the performance gate.

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

Follow-up samples after the Adler reduction-window change remained noisy and
still failed the faster-than-both requirement. Representative failing samples:
Adler-32 was about `0.90x` C / `1.63x` Rust in one Cranelift run and about
`0.90x` C / `0.91x` Rust in one LLVM-probe run; XXHash64 and CRC32 also moved
between pass/fail depending on C/Rust single-run baseline variance.
`run_port_algorithm_benchmarks.shs` now accepts `SIMPLE_BENCH_SAMPLES=N` and
reports median MB/s per implementation; a 2-sample smoke still failed the speed
gate, with Adler-32 at `0.71x` C / `0.75x` Rust.

The benchmark harness now also uses longer iteration windows for the measured
rows so sub-millisecond rows do not dominate the ratios: XXHash64 `1600`,
CRC32 `160`, Adler-32 `800`, and ChaCha20 `120` iterations. A 3-sample median
run after that hardening still failed the faster-than-both gate:

| Family | Algorithm | C median MB/s | Rust median MB/s | Simple median MB/s | Simple/C | Simple/Rust | Status |
|--------|-----------|---------------|------------------|--------------------|----------|-------------|--------|
| Non-crypto hash | XXHash64 | 14653 | 8578 | 8339 | 0.57x | 0.97x | Below C/Rust |
| Checksum | CRC32 | 457 | 456 | 403 | 0.88x | 0.88x | Below C/Rust |
| Checksum | Adler-32 | 2598 | 2623 | 2451 | 0.94x | 0.93x | Below C/Rust |
| Stream cipher | ChaCha20 | 308 | 347 | 361 | 1.17x | 1.04x | Faster than C/Rust |

Attempted CRC32 lazy table caching passed interpreter KATs but segfaulted in the
native benchmark; it was reverted and tracked in
`doc/08_tracking/bug/crc32_native_global_table_cache_segfault_2026-05-13.md`.
A direct 1024-byte `[u8]` literal table was also rejected: interpreter KATs
passed, but native CRC32 checksum parity failed, tracked in
`doc/08_tracking/bug/native_u8_array_literal_not_packed_2026-05-13.md`.
XXHash64 now avoids duplicate `* p2` work inside rotate expressions in the
one-shot stripe, merge, and 8-byte tail paths. Checksum parity still passes, and
one 3-sample run showed Simple XXHash64 at `13242 MB/s`, but the row remains
below C in that same run (`0.91x` C / `1.67x` Rust), so it is not complete.
An Adler-32 5552-byte `u32` accumulator variant was also rejected after it
preserved KATs but regressed the benchmark smoke to `0.89x` C / `0.89x` Rust;
the current 355328-byte `u64` window remains the better measured source form.

### Remaining Performance Matrix

This matrix is the plan-of-record for the unfinished rows. `TBD` means no
apples-to-apples C/Rust/Simple parity benchmark is accepted yet. A row is not
complete until correctness passes and both ratio columns are above `1.00x`.

| Family | Algorithms | Simple/C | Simple/Rust | Remaining compiler/plugin work |
|--------|------------|----------|-------------|--------------------------------|
| Non-crypto hash | XXHash64 | 0.57x | 0.97x | General MIR CSE/GVN for repeated rotates, shifts, adds, xors, and multiply-derived addressing |
| Checksum | CRC32 | 0.88x | 0.88x | Static table materialization without native global-cache crash or native `[u8]` literal corruption, table lookup hoisting, typed byte slice lookup facts |
| Checksum | Adler-32 | 0.94x | 0.93x | Weighted byte-reduction plugin, measured median gate, range/bounds proof |
| Stream cipher | ChaCha20 | 1.17x | 1.04x | Keep as canary; prevent regressions while generalizing typed word-state lowering |
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
- Verification: targeted MIR/runtime tests, package checks, release driver build, checksum parity for the port benchmark, and cipher/compress gate `passed=13 skipped=0 failed=0`.
 
## Known Blockers

- None for the core cipher/compression gate as of 2026-05-13. The broader optimization plan remains open until every measured row beats both C and Rust baselines.
- Performance blocker: CRC32 lazy module-level table caching currently crashes native code; see `doc/08_tracking/bug/crc32_native_global_table_cache_segfault_2026-05-13.md`.
- Performance blocker: CRC32 direct `[u8]` literal table materialization currently corrupts native checksum parity; see `doc/08_tracking/bug/native_u8_array_literal_not_packed_2026-05-13.md`.
