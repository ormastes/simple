# Kernel Zstd Adapter Compression Facade Import

Date: 2026-05-12
Status: Resolved 2026-05-13

`test/unit/os/kernel/loader/zstd_decompress_spec.spl` was a known blocker for the cipher/compression algorithm gate. The compression facade helpers did not resolve through `std.common.compress.{...}` in the current checkout.

Resolution: added the shared `src/lib/common/compress.spl` facade with codec dispatch, option validation, streaming finish helpers, and public re-exports for the compression framework.

Verification: `src/compiler_rust/target/release/simple test test/unit/os/kernel/loader/zstd_decompress_spec.spl --mode=interpreter --no-cache` passes 2 examples, 0 failures. The strict core cipher/compression gate reports `passed=13 skipped=0 failed=0`.
