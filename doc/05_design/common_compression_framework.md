# Detail Design — `common_compression_framework`

## Shared API

- `CompressionCodec`: selects wire format family.
- `CompressionLevel`: validated wrapper to keep codec-specific ranges explicit.
- `CompressionOptions`: keeps one stable call shape across codecs.
- `CompressionError`: normalized failure surface for malformed or unsupported inputs.
- `CompressionEncoderState` / `CompressionDecoderState`: append-and-finish streaming façade.

## LZ4 design

- Raw block format is implemented directly.
- Frame writer emits a standard LZ4 frame with descriptor checksum and optional content checksum.
- Compressor uses a greedy backward search bounded by the standard 64 KiB offset window.

## Zstd design

- Writer emits a valid standard frame using raw or RLE blocks.
- Reader accepts raw and RLE blocks and rejects compressed blocks explicitly.
- This preserves standard-tool decode compatibility for emitted frames while keeping the phase small enough to land cleanly.

## XZ/LZMA2 design

- Writer emits an XZ stream with one block, one LZMA2 filter, CRC32 checks, and uncompressed LZMA2 chunks.
- Reader validates XZ header/footer/index structure and accepts uncompressed LZMA2 chunks for the first phase.
- Compressed LZMA2 chunks remain an explicit follow-up phase.

## Error handling

- Bad magic or malformed framing returns `InvalidHeader` or `CorruptStream`.
- Short reads return `TruncatedInput`.
- Check mismatches return `ChecksumMismatch`.
- Unsupported standard features return `UnsupportedFeature`.
