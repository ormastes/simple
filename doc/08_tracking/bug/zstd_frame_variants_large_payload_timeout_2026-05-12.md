# Zstd Frame Variants Large Payload Timeout

Date: 2026-05-12
Status: Open

`test/unit/lib/common/zstd_frame_variants_spec.spl` is a known blocker for the cipher/compression algorithm gate. The large 70,000-byte single-segment payload path times out in interpreter mode.

Current gate handling: strict mode must fail or time out on this spec; `CIPHER_COMPRESS_ALLOW_KNOWN_FAIL=1` may skip it while unrelated algorithm work is verified.

Next step: profile the large-payload literal/sequence loops and replace repeated byte-at-a-time work with existing batch copy and typed-byte primitives where the format invariants prove bounds.
