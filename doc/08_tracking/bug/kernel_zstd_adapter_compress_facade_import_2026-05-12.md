# Kernel Zstd Adapter Compression Facade Import

Date: 2026-05-12
Status: Resolved 2026-05-27

`src/os/kernel/loader/zstd_decompress.spl` imported `common.compress.{CompressionError, decompress_bytes}` — two bugs in one line:
1. Missing `std.` prefix (`common.compress` is not a valid path; resolves as `std.common.compress`).
2. `decompress_bytes` does not exist in the facade; the actual export is `zstd_decompress_frame` (from `std.common.compress.zstd`).
3. Earlier adapter revisions hand-matched specific `CompressionError` variants
   instead of using the shared `message()` method, making the adapter brittle as
   the common error enum evolved.

Resolution:
- `std.common.compress` now exports `compress_bytes` and `decompress_bytes`
  alongside `default_compression_options`.
- `compress_bytes(data, options)` routes the shared facade to the requested
  codec. The zstd path uses the existing `zstd_compress_frame`.
- `decompress_bytes(data, Some(codec))` dispatches to the requested codec.
  `decompress_bytes(data, nil)` detects zstd/lz4/gzip frame headers and returns
  `CompressionError.InvalidHeader("codec auto-detect failed")` when no known
  header is present.
- `src/os/kernel/loader/zstd_decompress.spl` now uses the shared facade and
  returns the facade error message.

Verification refreshed 2026-05-27:
- `bin/simple check src/lib/common/compress/utilities.spl src/lib/common/compress/deflate.spl src/lib/common/compress/__init__.spl src/os/kernel/loader/zstd_decompress.spl test/unit/os/kernel/loader/zstd_decompress_spec.spl`
- `bin/simple test test/unit/os/kernel/loader/zstd_decompress_spec.spl --mode=interpreter --clean` — 2 passed, 0 failed.
- `bin/simple test test/unit/lib/common/zstd_sequence_fse_tables_spec.spl --mode=interpreter --clean` — 3 passed, 0 failed.
