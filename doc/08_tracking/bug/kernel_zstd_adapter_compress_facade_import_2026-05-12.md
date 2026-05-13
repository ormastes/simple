# Kernel Zstd Adapter Compression Facade Import

Date: 2026-05-12
Status: Open

`test/unit/os/kernel/loader/zstd_decompress_spec.spl` is a known blocker for the cipher/compression algorithm gate. The compression facade helpers do not resolve through `std.common.compress.{...}` in the current checkout.

Current gate handling: strict mode must fail on this spec; `CIPHER_COMPRESS_ALLOW_KNOWN_FAIL=1` may skip it while unrelated algorithm work is verified.

Next step: decide whether the kernel loader should import the shared compression facade directly or use a small OS-local adapter that preserves the loader boundary.
