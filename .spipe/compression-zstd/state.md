# compression-zstd

## Status: IN PROGRESS

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

## Scope — Supported
- Zstd magic frame (0xFD2FB528)
- Frame header: FHD, window descriptor, dictionary_id (0-byte = no dict), FCS
- Block header: Raw, RLE, Compressed blocks
- Literals section: Raw, RLE, Huffman-compressed, Treeless
- Huffman weight decoding via FSE
- FSE table construction (spread + delta) for LL, ML, OF sequences
- Sequence decoding with predefined distribution tables + compressed-mode tables
- Match copy with rep-offset history (rep1/rep2/rep3)
- Content checksum parsing (skipped, not verified)
- Skippable frames (skip past)
- Chained frames

## Scope — Deferred (Unsupported, returns Err)
- Dictionary mode (Dictionary_ID present in frame header)
- XXH64 content checksum verification
- Repeat-mode FSE table carry across blocks

## Files
- `zstd/bit_reader.spl`   — LSB forward + MSB-from-end reverse readers
- `zstd/frame.spl`        — Frame/block header parsing
- `zstd/fse.spl`          — FSE table build + decode
- `zstd/huffman.spl`      — Huffman literals decoder (weights via FSE)
- `zstd/literals.spl`     — Literals section dispatch
- `zstd/sequences.spl`    — Sequence section decode + predefined tables
- `zstd/blocks.spl`       — Block dispatch + match copy
- `zstd/decoder.spl`      — Top-level `zstd_decode`
- `zstd/mod.spl`          — Re-exports

## Work done
1. Created `.spipe/compression-zstd/state.md`
2. Implemented all zstd/ source files (see Files above)
3. Created `test/unit/lib/nogc_sync_mut/compression/zstd/zstd_basic_spec.spl`
4. Created `src/lib/common/compress/zstd.spl` facade
5. Updated `src/lib/common/compress/__init__.spl`
6. Committed with `jj commit`
