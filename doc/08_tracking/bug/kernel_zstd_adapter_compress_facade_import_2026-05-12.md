# Kernel Zstd Adapter Compression Facade Import

Date: 2026-05-12
Status: Resolved 2026-05-19

`src/os/kernel/loader/zstd_decompress.spl` imported `common.compress.{CompressionError, decompress_bytes}` — two bugs in one line:
1. Missing `std.` prefix (`common.compress` is not a valid path; resolves as `std.common.compress`).
2. `decompress_bytes` does not exist in the facade; the actual export is `zstd_decompress_frame` (from `std.common.compress.zstd`).
3. The `match` on `CompressionError` referenced six variants (`UnsupportedFeature`, `ChecksumMismatch`, `CorruptStream`, `SizeLimitExceeded`, etc.) that do not exist in `src/lib/common/compress/types.spl` (which defines `TruncatedInput | InvalidHeader | CorruptData | Unsupported | OutputTooSmall | Other`).

Resolution: rewired the kernel adapter to use the symbols that are actually exported today:
- `use std.common.compress.types.{CompressionError}` — correct path with `std.` prefix.
- `use std.common.compress.zstd.{zstd_decompress_frame}` — existing export, returns `Result<[u8], CompressionError>`.
- Collapsed the broken variant match to `error.message()` (provided by the `CompressionError` impl in `types.spl`).

Note: `src/lib/common/compress.spl` (a top-level facade file) does not exist in the tree. The previous resolution claim was incorrect. The `__init__.spl` facade under `src/lib/common/compress/` also does not export `compress_bytes`, `decompress_bytes`, or `default_compression_options`. The test spec (`test/unit/os/kernel/loader/zstd_decompress_spec.spl`) calls those functions and will require a follow-up to add them to the facade and re-export from `__init__.spl`. The second test's expected error message "codec auto-detect failed" will also need to be reconciled with `zstd_decompress_frame`'s actual error text once that facade is in place.
