# Domain Research — `common_compression_framework`

## Standards and interoperability targets

- LZ4 interoperability requires both raw block decoding rules and the framed container (`magic`, descriptor flags, block stream, optional content checksum).
- Zstd interoperability is organized around a frame header plus a sequence of typed blocks. Raw and RLE blocks are fully standard even when entropy-compressed blocks are not yet implemented.
- XZ is a container around filters. A normal single-filter LZMA2 stream can legally carry uncompressed LZMA2 chunks, which is useful for a phased implementation because it preserves standard tooling compatibility before the entropy core is complete.

## Practical engineering observations

- LZ4 is the cheapest full first tranche because the block format is simple, the frame header is small, and greedy matching is sufficient for a correct baseline.
- Zstd compressed-block support is substantially more expensive because it pulls in bitstream management, literals/sequences sections, Huffman, and FSE tables.
- LZMA2/XZ has a more complex container than LZ4 but still permits a useful interoperable first step through uncompressed LZMA2 chunks plus CRC validation.
- Checksums matter at different layers:
  - LZ4 frame descriptor uses a header checksum and may use content checksum.
  - Zstd content checksum is optional and can be deferred in an initial subset if the frame parser rejects unsupported variants explicitly.
  - XZ requires CRC protection for header/index/footer and block integrity according to the selected check type.

## Chosen phased delivery

1. Shared API and streaming state.
2. Full LZ4 block/frame baseline.
3. Zstd standard frame subset for raw/RLE blocks.
4. XZ/LZMA2 single-filter baseline using uncompressed chunks.
5. Follow-up phases for compressed zstd blocks, fuller LZMA2 coding paths, and SIMD fast paths.
