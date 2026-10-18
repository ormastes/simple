# gzip / DEFLATE RFC 1951 + 1952 hardening findings (2026-10-18)

Spec: test/01_unit/lib/nogc_sync_mut/compression/gzip_rfc1951_1952_spec.spl (97 examples).
Binary: Rust seed bin/local/seed_simple (9c45d2bf601ab93e), interpreter + JIT.

## Fixed in this change
- **JIT divergence** (round trip printed `ok=0` under JIT): see
  seed_jit_untyped_to_u8_push_double_untag_2026-10-18.md. Worked around with typed idioms.
- `deflate_distance_code` returned 28 for every distance > 16384; distances 24577..32768
  must use code 29 (RFC 1951 3.2.5). 8192 distances mis-encoded (only reachable if lz77
  ever emits a match > 24576 back; today it does not, so latent).
- Dynamic header accepted HDIST 31/32 (RFC/zlib: <= 30) and accepted incomplete
  code-length / literal / distance codes (only the single one-bit code is allowed).
- A gzip member whose DEFLATE body never set BFINAL, or was empty, decoded successfully.
  `gzip_decompress`/`gzip_validate`/facade now use `inflate_complete`. Raw `inflate` keeps
  the RFC 7692 sync-flush leniency by design.
- `gzip_header_create(filename, ...)` mapped any char outside a 9-char whitelist to 0x00
  (silent truncation of FNAME); now writes the UTF-8 bytes + terminator.
- `stream.spl` `gzip_stream_text_to_bytes` had the same lossy mapping; now `text.bytes()`.
- Dead code removed (unreachable defensive branches; ~300 lines of an uncalled generic
  Huffman tree codec in huffman.spl; `char_to_byte`; `bitstream_reader_pos`).

## Decisions / still open
- Multi-member gzip (RFC 1952 2.2) is REJECTED (single member only); spec'd as such.
  zlib/gunzip accept concatenated members.
- Errors are nil (facade: []), not a typed `Result`; a typed error was not added.
- `stream.spl` `byte_to_char` / `gzip_stream_bytes_to_text` are still lossy ("?" fallback).
- compress.spl, stream.spl, lz77.spl, deflate.spl are not at 100% coverage (compress.spl and
  stream.spl analysis helpers have no callers in this spec).
- **JIT perf/memory**: compressing 30,064 bytes (build/probe/gzip_far.spl): JIT wall=30.2s
  RSS=7.75 GB vs interpreter wall=10.6s RSS=0.10 GB. Looks like O(n^2) array copying in the
  JIT (also: JIT `push` through an `[Any]` tuple slot mutates the caller's array). Not fixed.
