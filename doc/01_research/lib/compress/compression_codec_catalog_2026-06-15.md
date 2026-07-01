<!-- codex-research -->

# Research — Compression Algorithm / Format / Codec Catalog (custom-type-first)

Created 2026-06-15. Sibling of the crypto and search catalogs. Companion plan:
[`doc/03_plan/lib/compress/custom_type_alpha_compression_team_plan_2026-06-15.md`](../../../03_plan/lib/compress/custom_type_alpha_compression_team_plan_2026-06-15.md).

**Builds on existing research — does not re-catalogue it.** The full pure-Simple
codec target, in-tree state, and SIMD tier are already specified in
[`../common_compression_framework.md`](../common_compression_framework.md),
[`../common_compression_framework_local.md`](../common_compression_framework_local.md),
and `doc/01_research/compiler/compression/compress_simd_patterns_2026-05-02.md`.
This doc adds the **broad external map + the custom-type layer** on top.

Shared custom-type foundation is defined once in the **crypto plan §Phase-0**
(`src/lib/common/bytes/`); `RingWindow`/`BitReader`/`BitWriter`/checksums there
are the LZ + entropy primitives — do not redefine.

## Purpose & target
Same wave goal: **improve the Simple language**. Compression is the **bit-stream
stressor** — `BitReader`/`BitWriter`, entropy tables, and LZ windows exercise
`me`-self-mutation, fixed-width integer types, and tight inner loops harder than
anything else.

## In-tree status (see common_compression_framework for detail)
| Codec | In-tree | Path | State |
|-------|---------|------|-------|
| LZ4 (block+frame) | yes | `src/lib/common/compress/lz4.spl` | subset; speed-parity plan `pure_simple_lz4_zstd_speed_parity.md` |
| Zstd | yes | `src/lib/common/compress/zstd.spl` | subset (rejects non-default level/checksum/dict) |
| LZMA2/XZ | yes | `src/lib/common/compress/lzma2.spl` | subset |
| DEFLATE/gzip | yes | `src/lib/common/compress/deflate.spl`, `gzip.spl` | |
| Brotli | yes | `src/lib/common/compress/brotli.spl` | |
| Huffman / LZ77 | yes | `src/lib/common/huffman/`, `lz77/` | entropy + LZ primitives |
| adler32 / crc | yes | `src/os/crypto/adler32.spl` | move to `bytes/checksum.spl` |
| zstd loader adapter | yes | `src/os/kernel/loader/zstd_decompress.spl` | thin over `common.compress` |

**Conclusion:** compression is mid-mature — façade + 3 codecs exist but
subset-only. New work = custom-type refactor + finish the staged subset behind
the shared library + alpha SIMD/scalar parity. Duplicate codec paths in
consumers are tech debt (per existing research) — unify, don't fork.

## Catalog (external map; plan picks staged subset)
- **Primitive:** RLE/PackBits, delta/BCJ filters, bit-packing/FOR/PFOR,
  dictionary substitution, MTF, BWT (suffix-array), predict+residual.
- **Entropy:** Huffman (static/dynamic/canonical), arithmetic, range coder,
  ANS (rANS/tANS/FSE/Huff0), Golomb/Rice, Elias/Exp-Golomb, varint/LEB128/
  StreamVByte.
- **LZ family:** LZ77/LZSS/LZ4/LZO/Snappy/FastLZ/QuickLZ, LZ78/LZW, DEFLATE,
  LZMA/LZMA2, Brotli, Zstd, LZFSE, LZHAM.
- **Block-sorting / high-ratio:** bzip2 (BWT+MTF+RLE+Huffman), libbsc, PPM/PPMd,
  PAQ/LPAQ, ZPAQ, context mixing (research-tier, not for new pure-Simple impl).
- **Single-stream formats:** raw DEFLATE, zlib, gzip, bzip2, xz, lzma, lzip,
  zstd, lz4 frame, brotli, lzop, .Z, Snappy framed, LZFSE, bsc, zpaq.
- **Archive/container:** tar/pax/cpio/ar, ZIP, 7z, RAR, CAB/CHM (LZX/MSZIP),
  WIM/ESD, XAR, LHA/ARJ/ARC/ZOO/ACE, DMG, SquashFS/CramFS/EROFS, RPM/DEB.
- **Image/media (codecs, not general compressors):** PNG(DEFLATE+filters), GIF
  (LZW), JPEG/JPEG-LS/JPEG2000/JPEG-XL, WebP, AVIF, HEIF, TIFF, OpenEXR, QOI;
  audio FLAC/ALAC/WavPack; video FFV1/H.264/H.265/AV1 — out of scope for the
  general-purpose library, noted for completeness.
- **Index/bitmap compression:** roaring/EWAH/WAH, FOR/BP128, Rice/Golomb (shared
  conceptually with the search plan's posting-list work).

### Legacy / avoid for new impl
RAR (unRAR restriction), QuickLZ/LZO (GPL or dual), PAQ (GPL), ACE/StuffIt
(proprietary). Decode-only/compat behind gates if ever needed.

## Custom-type layer (compression-domain, atop `src/lib/common/bytes/`)
| Primitive today | Custom type | Behavior |
|-----------------|-------------|----------|
| `[u8]` in/out | `Plaintext` / `Compressed` (over `ByteSpan`) | prevents in/out mixups |
| bit cursor | `BitReader`/`BitWriter` (foundation) | `me read_bits/put_bits`, order invariant |
| LZ history | `RingWindow` (foundation) | `match_len`, `copy_match`, distance invariant |
| `i64` match | `LzToken` enum (`Literal`/`Match{len,dist}`) | tagged, no `(len,dist)` tuple corruption |
| Huffman table | `HuffTable` / `FseTable` | build from freqs, `decode_sym(BitReader)` |
| freq counts | `SymbolFreqs` | `me bump(sym)`, normalize |
| `i64` checksum | `Crc32`/`Adler32` (foundation) | incremental |
| options | `CompressionOptions` (exists) | keep façade shape; tighten semantics |

`LzToken` enum is the deliberate fix for the known `(i64,i64,text,text)` tuple
element corruption (memory) — tagged custom types instead of tuples.

## C reuse license gate
| Library | License | Posture |
|---------|---------|---------|
| zlib / libdeflate | zlib / MIT | **permissive** oracle (DEFLATE) |
| libzstd / FiniteStateEntropy | BSD | **permissive** oracle (Zstd/FSE) |
| liblz4 | BSD-2 | **permissive** oracle |
| brotli | MIT | **permissive** oracle |
| XZ Utils / liblzma | 0BSD/PD | **permissive** oracle (xz/LZMA2) |
| LZMA SDK | public domain | **permissive** |
| bzip2/libbz2 | bzip2 lic | **permissive** |
| FastLZ / liblzf | MIT/BSD | **permissive** (embedded) |
| heatshrink | ISC | **permissive** (tiny embedded) |
| libarchive | BSD | **permissive** (containers) |
| LZO / QuickLZ | GPL or dual | **copyleft ⇒ write own C** |
| UnRAR | restricted | **cannot reuse for compression** ⇒ skip |
| 7-Zip unRAR code | mixed/restricted | avoid restricted parts |

## Verification implications (extends common_compression_framework)
- Alpha: forced scalar vs AVX2/NEON helper, **and** C oracle (zstd/lz4/zlib) vs
  pure-Simple, byte-for-byte round-trip + corruption handling + typed errors.
- Test vectors as typed fixtures; full round-trip not subset acceptance.
- Reuse the existing verification command set in `common_compression_framework`.
