# compression-brotli — state

## Status: DONE

## Research findings
- Full brotli decoder already exists at `src/lib/nogc_sync_mut/compression/brotli/`
  - `decoder.spl` — `brotli_decode(input: [u8]) -> Result<[u8], CompressionError>`
  - `encoder.spl` — `brotli_encode(data: [u8]) -> [u8]`, `brotli_encode_uncompressed(data: [u8]) -> [u8]`
  - `mod.spl` — public re-exports
  - `bit_reader.spl`, `bit_writer.spl`, `decoder_block.spl`, `decoder_huffman.spl`, `decoder_tables.spl`
- `src/lib/common/compress/` is a facade layer mirroring the nogc primitives
  - `gzip.spl` wraps nogc gzip with simple `[u8] -> [u8]` API
  - `__init__.spl` re-exports facade symbols
  - `types.spl` defines `CompressionCodec` (already has `brotli` variant) and `CompressionError`

## Work done
1. Created `src/lib/common/compress/brotli.spl` — facade wrapping `brotli_decode`/`brotli_encode`
2. Updated `src/lib/common/compress/__init__.spl` to re-export brotli symbols
3. Committed with jj
