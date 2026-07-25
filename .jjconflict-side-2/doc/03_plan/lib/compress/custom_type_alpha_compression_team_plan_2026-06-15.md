# Plan — Custom-Type Alpha Compression Team

Created 2026-06-15. Companion research:
[`doc/01_research/lib/compress/compression_codec_catalog_2026-06-15.md`](../../../01_research/lib/compress/compression_codec_catalog_2026-06-15.md).
Sibling of the crypto (template) and search plans. Builds directly on the
existing compression program:
[`doc/01_research/lib/common_compression_framework.md`](../../../01_research/lib/common_compression_framework.md)
and plan `pure_simple_lz4_zstd_speed_parity.md`.

## Prime directive
Same wave goal: **#1 deliverable is improving the Simple language**.
Compression is the **bit-stream + tight-loop stressor** (`BitReader/Writer`,
entropy tables, LZ window). Custom types carry behavior; primitive workarounds
get filed, never normalized.

## Dependency — shared foundation (BARRIER)
**Prerequisite:** crypto plan §Phase-0 (`src/lib/common/bytes/`). The LZ +
entropy primitives — `BitReader`, `BitWriter`, `RingWindow`, `Crc32`, `Adler32`,
endian int views — live there and are **shared with the search plan**. Do not
redefine. Compression fan-out starts only after the barrier lands. Move existing
`src/os/crypto/adler32.spl` into `bytes/checksum.spl` during Phase 0.

## Mode: alpha
Reuse `dual_backend.spl`. Alpha compares forced-scalar vs SIMD helper paths
**and** C oracle (zstd/lz4/zlib) vs pure-Simple, byte-for-byte round-trip,
fail-closed on mismatch. Codecs already exist as **subsets** — this refactors
them onto custom types and **finishes the staged subset**, unifying duplicate
consumer paths (per existing research; duplication is tech debt).

## C-implementation policy
Permissive (zlib/libdeflate, libzstd/FSE, liblz4, brotli, liblzma/LZMA SDK,
libbz2, FastLZ, heatshrink, libarchive) ⇒ vendor/bind under
`src/runtime/vendor/**` as alpha oracle. Copyleft (LZO, QuickLZ) ⇒ write own
minimal C oracle. UnRAR/restricted ⇒ skip entirely. Gate table in research doc.

## Phases

### Phase 0 — Foundation barrier
Consume crypto §Phase-0; relocate checksums into `bytes/`. Add compression-domain
types in `src/lib/common/compress/types.spl` (extend existing): `LzToken` enum
(`Literal`/`Match{len,dist}`) replacing `(i64,i64,...)` tuples, `HuffTable`,
`FseTable`, `SymbolFreqs`, `Plaintext`/`Compressed` newtypes. Keep the public
façade shape (`CompressionCodec`, `CompressionOptions`, `compress_bytes`,
`try_compress_bytes`, `encoder_finish_checked`).

### Phase 1 — Codec refactor onto custom types (disjoint scope)
| Sub-team | Scope (files) | Custom types | C oracle |
|----------|---------------|--------------|----------|
| C1 LZ4 | `compress/lz4.spl` | `RingWindow`,`LzToken`,`ByteBuffer` | liblz4 |
| C2 DEFLATE/gzip | `compress/deflate.spl`,`gzip.spl`,`huffman/` | `HuffTable`,`BitReader/Writer` | zlib/libdeflate |
| C3 Zstd | `compress/zstd.spl` | `FseTable`,`HuffTable`,`SymbolFreqs` | libzstd/FSE |
| C4 LZMA2/XZ | `compress/lzma2.spl` | range coder over `BitReader` | liblzma |

Staged subset (finish, not expand): LZ4 block+frame, DEFLATE/gzip, Zstd frame,
LZMA2/XZ frame — full round-trip, real levels, checksum, framed dictionary
(`dictionary_id`). bzip2/Brotli-complete/PPMd/ZPAQ deferred. Strict `block_mode`
semantics per existing research (lz4 block+frame; zstd/lzma2 frame-only).

### Phase 2 — Hardening & parity
Corruption handling + typed `CompressionError`, duplicate-path unification
(consumers call `common.compress` only), SIMD helper specialization with scalar
oracle, alpha C-oracle parity. Run the `common_compression_framework`
verification command set.

## Multi-agent structure
Orchestrator (Opus) owns barrier + merges + language-item triage + commits.
4 Sonnet sub-agents, **disjoint files**, parallel in one message after barrier,
each told it has `advisor()`. Commit per lint-clean sub-batch (jj clobber risk).

## Language-improvement capture (first-class)
Expected hot spots (pre-seed): `(i64,i64,text,text)` tuple element corruption
(the reason `LzToken` is an enum), `me`-self-mutation on `BitWriter`/`RingWindow`
cursors (E1052), `array.get(n≥1)` corruption on the inner copy loop, fixed-width
integer/endian semantics, JIT string-method folding, generics on `HuffTable`
decode. File each via `bin/simple bug-add` / `doc/02_requirements/feature/`.
No items produced = red flag.

## Gates
`bin/simple test`, `bin/simple build lint`, compression + foundation specs green
(full round-trip, not subset), alpha scalar-vs-SIMD and C-oracle parity green,
`sh scripts/check/check-core-runtime-smoke.shs bin/simple`, `verify` →
`STATUS: PASS`.
