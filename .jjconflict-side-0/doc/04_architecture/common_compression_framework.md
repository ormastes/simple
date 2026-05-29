# Architecture — `common_compression_framework`
<!-- codex-architecture -->
<!-- codex-design -->

## Status

This document describes the currently landed architecture for `std.common.compress` as verified on 2026-05-01. It does not describe the original full-scope target as if it were already complete.

## Architectural intent

- `src/lib/common/compress/` is the owned compression surface.
- Public callers depend on `std.common.compress`; the kernel Zstd loader remains a thin adapter over the shared library.
- Codec logic, checksum helpers, and tier-specific hot-path helpers remain in `.spl`.
- SIMD specialization stays inside the library through the existing Simple-visible SIMD facilities; there is no second runtime dispatch layer.

## Public structure

- [src/lib/common/compress/mod.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/mod.spl:1)
  Owns facade validation, codec dispatch, and buffered finish wrappers.
- [src/lib/common/compress/types.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/types.spl:1)
  Owns `CompressionCodec`, `CompressionLevel`, `CompressionOptions`, `CompressionError`, and buffered state types.
- [src/lib/common/compress/utilities.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/utilities.spl:1)
  Owns shared validation, codec detection, checksums, byte helpers, and tier-selection helpers.
- [src/lib/common/compress/lz4.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/lz4.spl:1)
  Owns LZ4 raw-block and frame encode/decode.
- [src/lib/common/compress/zstd.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd.spl:1)
  Owns the current Zstd framed subset.
- [src/lib/common/compress/zstd_bits.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_bits.spl:1), [zstd_fse.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_fse.spl:1), [zstd_huf.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_huf.spl:1)
  Own the bitstream, FSE, and Huffman helpers used by the Zstd implementation.
- [src/lib/common/compress/lzma2.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/lzma2.spl:1)
  Owns XZ framing plus the currently supported LZMA2 subset.

## Stable contract

- `CompressionCodec` remains `lz4`, `zstd`, `lzma2`.
- `CompressionOptions` remains the shared option carrier.
- `try_compress_bytes` and `encoder_finish_checked` are the checked encode surfaces.
- `compress_bytes` and `encoder_finish` remain fail-fast wrappers over the checked paths.
- `decompress_bytes` auto-detects framed codecs and still needs an explicit hint for raw LZ4 blocks.
- Unsupported option combinations fail with `CompressionError.UnsupportedFeature`; the facade does not silently normalize them.

## Current codec support

### LZ4

- Supported:
  - raw block encode/decode
  - frame encode/decode with independent blocks
  - block checksum and content checksum handling
  - content-size emission and validation
  - multi-block frame handling
  - scalar/AVX2/NEON tier parity hooks used by focused tests
- Current facade restrictions:
  - `block_mode` may be `block` or `frame`
  - only facade level `1` is accepted for encode
  - dictionaries are rejected
  - raw-block mode rejects `checksum=true` and `content_size`
- Explicitly unsupported:
  - dependent-block frames
  - dictionary-backed frames

### Zstd

- Supported:
  - framed encode/decode through `CompressionCodec.zstd`
  - frame header parsing across the currently tested descriptor variants
  - frame content checksum emission and verification
  - concatenated frame decode
  - scalar/AVX2/NEON parity hooks used by focused tests
  - host `zstd` decode of the library's emitted frames
- Current facade restrictions:
  - `block_mode` must be `frame`
  - only facade level `3` is accepted for encode
  - dictionaries are rejected on encode
- Explicitly unsupported or partial:
  - dictionary-backed frames on decode
  - non-RLE sequence tables in compressed blocks
  - FSE-compressed Huffman weights
  - full general-purpose host-generated compressed-frame coverage cannot be claimed yet

### XZ/LZMA2

- Supported:
  - XZ container encode/decode for the library's current LZMA2 subset
  - CRC32 verification for block/footer checks
  - concatenated XZ stream decode with aligned stream padding
  - scalar/AVX2/NEON parity hooks used by focused tests
  - host `xz` decode of streams emitted by the library
- Current facade restrictions:
  - `block_mode` must be `frame`
  - `checksum` must remain `true` because the current encoder always emits CRC32
  - dictionaries are rejected
- Explicitly unsupported or partial:
  - range-coded compressed LZMA2 chunks
  - non-LZMA2 XZ filter chains
  - full host-generated `.xz` interoperability for compressed payloads

## Shared-kernel architecture

- Shared utility ownership currently covers:
  - codec detection
  - byte-order helpers
  - CRC32 and XXH32 helpers
  - buffered state append/reset helpers
  - tier selection for scalar/AVX2/NEON execution
- The codebase now exposes tier-forced helper entrypoints for focused parity tests, but it does not yet justify claiming that every planned shared-kernel refactor is complete across all codecs.

## Startup and hot-path constraints

- Importing `std.common.compress` does not require file IO, subprocesses, or generated tables.
- All current encode/decode work remains in-process.
- Reusable state is local to encoder/decoder calls and codec-local helpers; there is no persistent cross-process cache.

## Verification hooks

- The current verification surface is centered on focused specs under `test/unit/lib/common/`.
- The most trustworthy claims today are:
  - LZ4 parity and corruption coverage are strong.
  - Zstd checksum, header-variant, and concatenated-frame coverage exist for the landed subset.
  - XZ/LZMA2 coverage proves emitted-stream interoperability and explicit rejection of unsupported compressed chunks.
- Repository-wide `verify` cannot honestly report PASS for the original full feature scope until the remaining unsupported codec behavior and requirement/doc drift are resolved.
