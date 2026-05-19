# compression-zstd

## Status: PARTIAL — Raw/RLE/Skippable/Chained frames only

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
- Tests live at `test/unit/lib/nogc_sync_mut/compression/`
- Facade layer at `src/lib/common/compress/` (add `zstd.spl` + update `__init__.spl`)

## Scope — Implemented and Tested
- Zstd magic frame (0xFD2FB528) parsing
- Frame header: FHD, window descriptor, FCS
- Raw_Block: copy bytes directly
- RLE_Block: one byte repeated N times
- Content checksum skip (not verified)
- Skippable frames (skip past, produce no output)
- Chained frames (multiple frames concatenated)

## Scope — Deferred (returns Err(Unsupported))
- Compressed_Block (requires FSE + Huffman + sequences sections)
  - Literals section: Raw/RLE/Huffman-compressed/Treeless
  - FSE table construction and decoding (LL/ML/OF predefined distributions)
  - Huffman weight decoding via FSE
  - Sequence decoding with rep-offset history (rep1/rep2/rep3)
  - Match copy with overlap handling
- Dictionary mode (Dictionary_ID present in frame header)
- XXH64 content checksum verification
- Repeat-mode FSE table carry across blocks

## Known issues for future compressed-block implementation
When implementing Compressed_Block support, the following design issues must be
addressed (based on RFC 8878 review):
1. `ZstdRevBitReader` needs a persistent `byte_idx` field — cannot recompute
   from `len-1` on every read call; byte position must survive across calls.
2. FSE probability value semantics: raw value 0 triggers run-of-zeros; raw
   value 1 means prob=-1 (less-than-1); raw value N≥2 means prob=N-1.
3. 1-stream Huffman literals header: size_fmt==0 uses 10+10 bits (not 5+8).
4. Rep-offset history: when literal_length==0, offset==1 selects rep2 not rep1
   (RFC §3.1.1.1.3); offset==1 path must also rotate history.
5. FSE table builder: less-than-1 symbols (prob=-1) must be placed at table
   tail positions decrementing from table_size-1, not skipped in spread step.
6. `huff_decode_stream`: fast-table lookup must peek then consume `actual_bits`,
   not over-read with peek then re-read from original reader position (double-consumes).

## Files
- `zstd/bit_reader.spl`   — LSB forward + MSB-from-end reverse readers
- `zstd/frame.spl`        — Frame/block header parsing
- `zstd/blocks.spl`       — Raw/RLE block decode; Compressed_Block returns Err(Unsupported)
- `zstd/decoder.spl`      — Top-level `zstd_decode`
- `zstd/mod.spl`          — Re-exports

## Work done
1. Created `.spipe/compression-zstd/state.md`
2. Implemented zstd/ source files for Raw/RLE/Skippable/Chained support
3. Created `test/unit/lib/nogc_sync_mut/compression/zstd/zstd_basic_spec.spl`
4. Updated `src/lib/common/compress/zstd.spl` to re-export `zstd_decompress`
5. Updated `src/lib/common/compress/__init__.spl`
6. Committed initial scaffold with `jj commit`
7. Follow-up: removed broken fse.spl/huffman.spl scaffolding (6 known bugs,
   not wired up); cleaned blocks.spl to remove imports of nonexistent modules;
   stubbed Compressed_Block as Err(Unsupported)
