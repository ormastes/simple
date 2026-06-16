# Custom-Typed Algorithm Layers (search / crypto / compress)

Three additive, custom-types-first algorithm layers that wrap existing
KAT-passing primitive cores. They share one byte foundation and ride the alpha
dual-backend fail-closed seam. **Reuse these — do not reimplement an algorithm
or invent a parallel primitive type.**

## Why "additive typed", not in-place

Each domain already had 100+ primitive-based modules that hot parallel sessions
depend on. So these layers live in **new namespaces** that wrap the existing
cores rather than editing their signatures. Wrap, don't rewrite. New namespace
also means clean isolated landing (no collision with the cores' owners).

Two hard rules carried through all three:
- **No f64.** f64 is unreliable across backends here — all scoring/arithmetic
  (BM25, TF-IDF, IVF distances) is fixed-point integer.
- **Verify against an absolute oracle** (RFC/NIST KAT), never self-comparison.
  The test runner false-greens (it verifies file load, not always `it`-block
  execution); confirm with a `bin/simple run` probe — multi-second runtime is
  real, ~20ms means it did not execute.

## Shared foundation

`src/lib/common/bytes/` — `ByteSpan`, `ByteBuffer`, `BitReader`/`BitWriter`,
`U16/32/64` le/be, `RingWindow`, `Crc32`, `Adler32`.
Imports: lib code `use std.common.bytes.X`; specs `use lib.common.bytes.X`.

## The three layers

### Search — `src/lib/common/search/`
`types` + exact / multi / prefilter / simd_scan (Phase-1) +
`inverted_index`, `ranking` (BM25 / TF-IDF, fixed-point), `ann`
(IVF + kNN, fixed-point), `roaring` (bitmap). Facade in `__init__.spl`.

### Crypto (security) — `src/lib/common/crypto/typed/`
- `ctypes` — `Digest` / `MacTag` / `Nonce` / `AuthTag` / `Plaintext` /
  `Ciphertext` / `SecretKey` / `PublicKey` / `Signature` / `SharedSecret`, all on
  `ByteSpan`. Secret types ban raw `==`; use **constant-time `ct_eq`**.
- `hashes` (SHA-256/512/512-256, HMAC, HKDF), `aead` (AES-256-GCM,
  ChaCha20-Poly1305 — `AeadSealed{ct,tag}` / `AeadOpenResult` since there is no
  tuple/`Result<struct>` return), `asym` (Ed25519, X25519, ECDSA-P256).
- `seam` — alpha entry points (`alpha_run_span` / `alpha_run_digest`) taking
  `fn() -> ByteSpan` closures.

### Compress — `src/lib/common/compress/typed/`
`types` (`LzToken` enum `Literal(b)` / `Match(distance,length)`, `SymbolFreqs`,
canonical RFC 1951 `HuffTable`) + `lz4_typed`, `deflate_typed` (stored +
fixed-Huffman + gzip/CRC32), `zstd_typed` (frame + raw/RLE; FSE compressed-block
deferred), `lzma2_typed` (uncompressed + XZ frame + range coder; full LZMA model
deferred).

## Alpha dual-backend seam (fail-closed)

These layers run through `src/os/crypto/dual_backend.spl`. In **alpha** mode a
genuine runtime-vs-pure mismatch aborts the process (`rt_exit(70)`), never
returns a value — true fail-closed. A one-side-empty *absent-oracle* case
degrades to the present side (many callers have no real runtime oracle yet).
Full policy: `doc/07_guide/os/crypto_dual_backend.md`.

## References

- Plans: `doc/03_plan/lib/{search,crypto,compress}/custom_type_alpha_*_team_plan_2026-06-15.md`
- Catalogs: `doc/01_research/lib/{search,crypto,compress}/`
- Network sibling layer: `doc/07_guide/lib/networking/typed_network_and_algorithms.md`
