# compression-zstd

## Status: PARTIAL — Huffman literals + XXH64 checksum implemented; FSE sequences pending team4a (NOT CLOSED)
<!-- Huffman decoder (direct-weights), canonical table, 1-stream + 4-stream decoding, Treeless mode
     are now implemented in zstd/huffman.spl and wired into zstd/blocks.spl.
     XXH64 content checksum verification is now implemented (Team 5): zstd/xxh64.spl provides
     xxh64_checksum_lower32(); decoder.spl now verifies the 4-byte checksum instead of skipping it.
     FSE-compressed weights (header >= 128) and sequence decoding still return Err(Unsupported).
     Issue 1 (ZstdRevBitReader byte_idx), Issue 3 (10+10 bit size header), Issue 6 (peek/consume)
     are all fixed. Issues 2/4/5 belong to FSE — pending team4a fse.spl. -->

## Goal
Implement Zstd (RFC 8878) decompression in the standard library under
`src/lib/nogc_sync_mut/compression/zstd/`.

## Research findings
- Existing pattern: brotli decoder at `src/lib/nogc_sync_mut/compression/brotli/`
  - Uses `Result<[u8], CompressionError>` from `std.common.compress.types`
  - Named-field structs for reader state (not tuple returns)
  - Module re-exports via `mod.spl`
- `CompressionError` variants: `TruncatedInput(text)`, `InvalidHeader(text)`,
  `CorruptData(text)`, `Unsupported(text)`, `OutputTooSmall(text)`, `Other(text)`
- `CompressionCodec.zstd` already present in `std.common.compress.types`
- Tests live at `test/01_unit/lib/nogc_sync_mut/compression/`
- Facade layer at `src/lib/common/compress/` (add `zstd.spl` + update `__init__.spl`)

## Scope — Implemented and Tested
- Zstd magic frame (0xFD2FB528) parsing
- Frame header: FHD, window descriptor, FCS
- Raw_Block: copy bytes directly
- RLE_Block: one byte repeated N times
- Content checksum verification (XXH64 lower-32 per RFC 8878 §3.1.1)
- Skippable frames (skip past, produce no output)
- Chained frames (multiple frames concatenated)

## Scope — Implemented (this session)
- `zstd/huffman.spl` — new file:
  - `HuffEntry`, `HuffTable` structs
  - `huff_build_table(weights)` — canonical Huffman table from weight array
  - `zstd_lit_compressed_size()` — correct 10+10/14+14/18+18 bit header parsing (Issue 3 fixed)
  - `zstd_parse_weights()` — direct-weight (header < 128) path; FSE-weights stubbed
  - `huff_decode_stream()` — single-stream reverse-bit decode, peek/consume fix (Issue 6)
  - `huff_decode_4streams()` — 4-stream with jump table
  - `zstd_decode_huffman_literals()` — top-level: new-tree + treeless modes
- `zstd/blocks.spl` — updated:
  - `ZstdBlockState` gains `huff_table: HuffTable` field (Treeless carry)
  - Raw/RLE blocks thread `huff_table` through unchanged
  - Compressed_Block: Huffman (10) and Treeless (11) literal paths wired
  - `zstd_empty_huff_table()` and `zstd_huff_table_valid()` helpers
- `zstd/bit_reader.spl` — updated:
  - `ZstdRevBitReader`: `offset` field replaced by `byte_idx`+`bit_idx` (Issue 1 fixed)
  - `zstd_rbr_init`: sentinel-at-bit-0 edge case fixed
  - `zstd_rbr_read`: uses persistent `byte_idx`/`bit_idx` from struct

## Scope — Deferred (returns Err(Unsupported))
- Compressed_Block sequences (num_sequences > 0):
  - FSE table construction (LL/ML/OF predefined distributions) — pending team4a fse.spl
  - Huffman weight decoding via FSE (header byte >= 128) — pending team4a
  - Sequence decoding with rep-offset history — pending team4a + Issues 2/4/5
  - Match copy with overlap handling
- Dictionary mode (Dictionary_ID present in frame header)
- Repeat-mode FSE table carry across blocks

## Known issues status
1. FIXED — `ZstdRevBitReader` now has persistent `byte_idx`+`bit_idx` fields.
2. PENDING (team4a) — FSE probability semantics: raw 0=run-of-zeros, 1=prob=-1, N≥2=N-1.
3. FIXED — `zstd_lit_compressed_size()` uses correct 10+10/14+14/18+18 bit packing.
4. PENDING (team4a) — Rep-offset history: literal_length==0 + offset==1 selects rep2.
5. PENDING (team4a) — FSE table builder: prob=-1 symbols placed at tail positions.
6. FIXED — `huff_decode_stream`: peek(max_bits) then consume(entry.num_bits) from original reader.

## Files
- `zstd/bit_reader.spl`   — LSB forward + MSB-from-end reverse readers (Issue 1 fixed)
- `zstd/frame.spl`        — Frame/block header parsing
- `zstd/blocks.spl`       — Raw/RLE/Huffman/Treeless block decode; FSE sequences pending
- `zstd/huffman.spl`      — Huffman decoder: weight parsing, table build, 1/4-stream decode
- `zstd/xxh64.spl`        — XXH64 hash: `xxh64_checksum_lower32(data)` → lower 32 bits of XXH64
- `zstd/decoder.spl`      — Top-level `zstd_decode` (checksum verification wired in)
- `zstd/mod.spl`          — Re-exports (includes `xxh64_checksum_lower32`)

## Work done
1. Created `.spipe/compression-zstd/state.md`
2. Implemented zstd/ source files for Raw/RLE/Skippable/Chained support
3. Created `test/01_unit/lib/nogc_sync_mut/compression/zstd/zstd_basic_spec.spl`
4. Updated `src/lib/common/compress/zstd.spl` to re-export `zstd_decompress`
5. Updated `src/lib/common/compress/__init__.spl`
6. Committed initial scaffold with `jj commit`
7. Follow-up: removed broken fse.spl/huffman.spl scaffolding (6 known bugs,
   not wired up); cleaned blocks.spl to remove imports of nonexistent modules;
   stubbed Compressed_Block as Err(Unsupported)
8. Team 4 session: implemented huffman.spl (direct-weights, canonical table, 1+4 stream),
   fixed ZstdRevBitReader (Issue 1), fixed size header parsing (Issue 3),
   fixed peek/consume in huff_decode_stream (Issue 6), wired into blocks.spl,
   threaded huff_table through ZstdBlockState for Treeless support
9. Team 5 session: implemented xxh64.spl (XXH64 hash, lower-32-bit extraction per RFC 8878);
   updated decoder.spl to verify content checksum (returns CorruptData on mismatch,
   TruncatedInput if bytes missing); updated mod.spl to export xxh64_checksum_lower32
