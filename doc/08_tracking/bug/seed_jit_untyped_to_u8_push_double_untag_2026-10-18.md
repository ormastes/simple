# Seed JIT: `.to_u8()` / push on an untyped (`Any`) value is mis-encoded (value >> 3)

Date: 2026-10-18. Found by: gzip hardening lane. Binary: Rust seed `bin/local/seed_simple`
(sha256 prefix 9c45d2bf601ab93e), default JIT mode. Interpreter mode is correct.

## Symptom
`build/probe/perf_baseline.spl` (gzip_compress_default + gzip_decompress, any size, even 0 bytes)
printed `ok=0 same=false` under JIT and `ok=65536 same=true` under
`SIMPLE_EXECUTION_MODE=interpreter`.

## Minimal repro
`build/probe/gzip_jit_repro.spl`: pushing `v.to_u8()` into `var bytes = bs[0]` (untyped array
taken from an `[Any]` tuple) stores `99` as `12` (99 >> 3) under JIT; annotating
`var bytes: [u8] = bs[0]` gives 99. Same for `x.to_u8()` where `x` is an UNTYPED fn
parameter (`gzip_footer_create(crc32, size)`: footer bytes came out as value << 3).

## Root cause (our side)
Untyped params / `[Any]` tuple slots carry tagged values; JIT `to_u8()` + `push` on them
double-(un)tags. Not fixed in the seed; worked around in .spl with typed idioms:
- `header.spl`: `gzip_header_create(... timestamp: i64, extra_flags: i64, os_type: i64) -> [u8]`,
  `gzip_footer_create(crc32: i64, size: i64) -> [u8]`, `var header: [u8]`, `.to_u8()` pushes.
- `huffman.spl`: bitstream writer keeps its byte buffer as `[i64]` (`var bytes: [i64] = bs[0]`)
  and converts to `[u8]` once in `bitstream_finish`.

## Status
Worked around; seed JIT bug itself still open (needs a fix in src/compiler_rust).
