# gzip / DEFLATE RFC 1951 + 1952 hardening findings (2026-10-18)

Spec: test/01_unit/lib/nogc_sync_mut/compression/gzip_rfc1951_1952_spec.spl (112 examples).
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
  `gzip_decompress`/`gzip_validate`/facade now decode each member with `inflate_member`
  (BFINAL required). Raw `inflate` keeps
  the RFC 7692 sync-flush leniency by design.
- `gzip_header_create(filename, ...)` mapped any char outside a 9-char whitelist to 0x00
  (silent truncation of FNAME); now writes the UTF-8 bytes + terminator.
- `stream.spl` `gzip_stream_text_to_bytes` had the same lossy mapping; now `text.bytes()`.
- Dead code removed (unreachable defensive branches; ~300 lines of an uncalled generic
  Huffman tree codec in huffman.spl; `char_to_byte`; `bitstream_reader_pos`).

- **Stored blocks > 65535 bytes** (found 2026-10-18 by host `gzip -dc` on our output):
  `deflate_block_stored` wrote one block with a 16-bit LEN truncated mod 65536, so
  `gzip_compress_none` of >= 64 KiB was corrupt (`invalid compressed data--length error`).
  Now split into <= 65535-byte stored blocks, BFINAL only on the last. Host gzip decodes all
  60 probe outputs (sizes 0..70000 x 3 data shapes x 4 levels) in JIT and interpreter.

## Decisions / still open
- Multi-member gzip (RFC 1952 2.2) is now SUPPORTED (round 2): members decode back to back, output is
  the concatenation, any bad member or trailing non-member bytes fail the file.
- Errors are nil (facade: []), not a typed `Result`; a typed error was not added.
- `gzip_stream_bytes_to_text` now returns nil unless the bytes are valid UTF-8 (was a lossy "?" fallback).
- Coverage: all 8 gzip modules at 100% decision coverage, 0 uncalled functions (uncalled,
  unexported helpers deleted; the nogc_async_mut re-export wrappers trimmed to the surviving API).
- **Fixed in round 2 -- O(n^2) memory/time**: the bit writer returned its whole byte array from every
  call (copy per symbol) and the bit reader returned a tuple holding the input array per bit.
  deflate now collects (value, nbits) pairs and packs once; inflate uses an integer bit offset and a
  9-bit lookup table. 30 KB compress+decompress (input: 30000 LCG bytes, g = (g*1103515245+12345) & 0x7fffffff, byte = (g>>16)&255, seed 12345, then its first 64 bytes repeated; level 6): JIT 30.2 s / 7.75 GB -> 0.48 s / 124 MB;
  interpreter 10.6 s -> 2.9 s. The old encoder also mis-coded distances > 24576 (fixed above), so
  its output for such inputs was corrupt; for all other inputs output is byte-identical.
- JIT hazard: `push` through an `[Any]` tuple slot mutates the caller's array, and untyped `[Any]`
  values passed to typed params stay tagged (test/fixtures/compiler/seed_jit_untyped_any_tag_repro/main.spl, `rev=` line); typed locals avoid it.
- **Fixed in round 3 -- memory DoS via many blocks** (independent reviewer, also on base): every block
  did `var out = history` and the core did `out = br[0]`, copying all output so far per block. Probe
  build/probe/review_blocks_{0,500,2000}.spl (1,032,001 bytes of history, N empty fixed blocks, 9 KB input):
  JIT RSS 76 MB / 606 MB / 2.19 GB; interpreter 2.3 s / 8.0 s / 25.4 s. Block decoders now only READ
  `history` and return the block's NEW bytes, appended once by the core (first block is moved, not copied);
  fixed tables are built once per stream. After: JIT RSS 76 / 93 / 103 MB, interpreter 2.1 s / - / 3.2 s at
  a flat 195 MB. Specs REQ-GZIP-190/191 (2000 empty blocks + budget) guard correctness; the RSS evidence is
  the probe. (These probe streams are raw DEFLATE, not gzip-wrapped, so host `gzip -dc` does not apply.)
