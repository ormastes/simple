# zstd FSE sequence decoder uses non-standard LSB backward reader — blocks real host frames

- **Status:** OPEN
- **Date:** 2026-06-30
- **Area:** `src/lib/common/compress/zstd_seq.spl`
- **Severity:** Medium (blocks decoding of any real host-zstd compressed block that carries sequences)
- **Found while:** implementing the fresh-table Compressed_Literals_Block decode path (`zstd_literals.spl` type 2).

## Summary

The Huffman *literal* decode path was just made real-zstd-compatible by reading
the literal bitstream with the standard MSB-first backward bit reader
(`ZstdMsbBackwardBits`, RFC 8478 Annex A). The FSE **sequence** decoder in
`zstd_seq.spl` still reads its bitstream with the Simple-internal **LSB-first**
`ZstdBackwardBits` reader (`zstd_bits_init` / `zstd_bits_peek` /
`zstd_bits_consume` at `_zstd_decode_fse_sequences`, `_zstd_read_sequence_state`,
`_zstd_read_sequence_bits`, `_zstd_advance_sequence_state`).

That LSB layout is self-consistent with Simple's own synthetic encoders (which
is all `zstd_sequence_fse_execution_spec.spl`'s 15 hand-built fixtures exercise),
but it does **not** match the byte/bit layout real zstd emits. Consequently any
real host frame whose compressed block contains ≥1 sequence fails to decode,
even though its literals now decode correctly.

Note: the FSE *Huffman-weight* decoder (`zstd_literals.spl`
`_zstd_parse_fse_compressed_weights`) already uses the correct MSB-first reader
(`zstd_msb_bits_*`) and decodes real frames — so FSE decoding *can* be done
correctly here; the sequence path simply was never migrated.

## Reproduction (minimal, host oracle)

`test/01_unit/lib/common/zstd_frame_variants_spec.spl` →
`it "decodes a host-generated frame for a mixed payload"` (the 1 remaining
failure; the spec is otherwise 18/19 green).

The frame is produced at runtime by `zstd -19 --no-check` over a 16384-byte
mixed payload. It is a single compressed block:

- Literals: type 2 (fresh-table), Size_Format 2 (4 streams), regenerated 2490,
  compressed 1914 bytes. **These now decode correctly** — verified via
  `zstd_parse_literals_section_for_test(frame, 10, 2235, nil)` returning 2490
  literals whose first 16 bytes (`0,97,97,32,17,98,98,32,…`) match the host
  `zstd -d` output byte-for-byte.
- Sequences: 1111 sequences, all FSE_Compressed mode (mode byte `0xA8` →
  LL=2, OF=2, ML=2).

End-to-end `zstd_decompress_frame(frame)` returns
`TruncatedInput("zstd bitstream bits")`, raised inside the LSB sequence FSE
decode (literals already succeeded). Host `zstd -d` decodes the same frame to
16384 bytes successfully.

## Root cause

`_zstd_decode_fse_sequences` (and the RLE variant) initialise the bitstream with
`zstd_bits_init` (LSB-first `ZstdBackwardBits`) and read FSE states / extra bits
with `zstd_bits_peek` / `zstd_bits_consume`. Real zstd sequence bitstreams are
backward MSB-first (same convention as the FSE weight stream and the Huffman
literal stream).

## Proposed fix (separate change; not done here to protect the green suite)

Migrate the sequence FSE decode in `zstd_seq.spl` to the MSB-first reader
(`ZstdMsbBackwardBits` / `zstd_msb_bits_*`, mirroring
`_zstd_parse_fse_compressed_weights` and the new
`_zstd_decode_huffman_stream_msb`). The 15 `zstd_sequence_fse_execution_spec.spl`
fixtures are hand-encoded for the LSB layout, so they must be regenerated to the
standard MSB layout in lockstep (or the decode must be proven bit-equivalent for
them) to keep that spec green. Because that spec is in the must-stay-green
regression set, the migration is deferred to a dedicated change with its own
fixture re-derivation rather than bundled with the literals fix.

## What works now

- `zstd_single_sequence_compress_spec.spl`: 10/10 (literals decode; the
  predefined-table sequence frame reaches the existing
  `zstd_seq.spl:242` "sequence decoding tables" guard exactly as the spec
  asserts).
- Fresh-table literal decode (1- and 4-stream, FSE or direct weights) is correct
  and over-read/trailing-bit safe (matches host rejection on malformed frames).
