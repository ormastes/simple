# Agent Task Breakdown — `common_compression_framework`

1. Create umbrella docs and requirements artifacts.
2. Add `src/lib/common/compress/` shared façade and type model.
3. Implement LZ4 block and frame encode/decode.
4. Implement Zstd frame subset encode/decode for raw/RLE blocks.
5. Implement XZ/LZMA2 subset encode/decode for single-filter uncompressed-chunk streams.
6. Add focused unit and interoperability tests.
7. Run targeted verification and record residual gaps.
