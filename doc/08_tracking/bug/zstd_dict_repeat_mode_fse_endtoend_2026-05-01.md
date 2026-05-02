# Zstd dictionary-frame Repeat_Mode FSE end-to-end test fixture not yet constructed

Date: 2026-05-01
Status: **Open / blocked on FSE Kraft bug + manual fixture cost**
Owner: T24 Wave-4 follow-up
Related: `doc/08_tracking/bug/bug_zstd_fse_huffman_weight_kraft_2026-05-01.md`,
`doc/09_report/verify_common_compression_framework.md` (`zstd.spl:1265`)

## Context

`test/unit/lib/common/zstd_dictionary_spec.spl` (10 cases, PASS 2026-05-01)
covers RFC 8478 §6 dictionary parsing positives + malformed cases, a
Raw_Block dict-referencing frame, the missing-dictionary error, **and**
end-to-end consumption of the seeded `huffman_table_state` via a
Treeless_Literals_Block. That test alone exercises:

- `_zstd_parse_dictionary` -> `ZstdDictionaryState{huffman, ...}`
- `_zstd_frame_dictionary_state` -> per-frame seeding slot
- `_zstd_decompress_frame_for_tier_with_dictionary` initialising
  `huffman_table_state` from `dictionary_state.huffman`
- `_zstd_parse_literals_section` (literals_type=3) consuming the seed and
  successfully decoding a 1-stream Huffman backward bitstream against the
  dict's tree.

It does **not** exercise the parallel seeding paths for sequence tables
or repeat offsets, because the Compressed_Block in the fixture uses
`sequence_count=0` (so `_zstd_parse_sequence_modes`,
`_zstd_parse_sequence_tables`, `_zstd_decode_fse_sequences`, and
`_zstd_execute_sequences` are never called).

## What is missing

A second end-to-end test: a Compressed_Block whose sequence section uses
**Repeat_Mode** for at least one of literals_length / offsets /
match_length (mode value `3`) so that the corresponding FSE decode table
must come from `dictionary_state.sequence_history` rather than a
predefined table. Concretely:

- `mode_byte = 0xFC` (LL=3, OF=3, ML=3) -> all three Repeat_Mode.
- `sequence_count >= 1`.
- A FSE backward bitstream that decodes correctly only when the dict's
  FSE tables are in use (i.e. distinguishable from the default
  predefined tables).
- For `repeat_offsets` coverage, the sequence's `offset_code <= 3` must
  pull `rep1`/`rep2`/`rep3` from `dictionary_state.repeat_offsets`
  rather than the RFC's hardcoded `(1, 4, 8)`. Then the executed copy
  must reach back into the dictionary's `content_prefix` window
  (`frame_out` starts as that prefix).

## Why this is hard

Hand-encoding a zstd backward FSE bitstream over the three sequence
streams (LL, OF, ML) requires:

1. Initialising 3 FSE states from the dict's tables. State init reads
   `accuracy_log` bits per stream from the bitstream (reverse order).
   For the existing dict's `0x10 0x3F` table headers (accuracy_log=5,
   counts=[16,16]), each state init costs 5 bits.
2. Per sequence, decoding offset_code -> N extra bits, literals_length
   code -> N extra bits, match_length code -> N extra bits, plus 3 FSE
   transition reads (one per stream) at table_log (5) bits each. For 1
   sequence: 3 * 5 init + offset_extra + ll_extra + ml_extra + 3 * 5
   transition >= 30+ bits, roughly 4 bytes of bitstream payload alone.
3. The bitstream is **read backwards** with the same end-marker rule as
   the Huffman stream. So the highest-bit byte must be non-zero, and
   the layout of bits in storage is "compressor-forward" while the
   decoder consumes them in reverse — easy to get wrong.
4. Choosing dict FSE tables that are observably different from the
   predefined distributions, so a pass against predefined would not
   accidentally green-light Repeat_Mode seeding.

This is solvable, but each step has its own bit-numbering pitfalls
similar in kind to the Huffman fixture (see
`test/unit/lib/common/zstd_dictionary_spec.spl` line ~155 for the
equivalent walk for the simpler Huffman case). The estimated effort is
1-3 hours of careful walk-through plus running the spec to confirm,
not minutes — exactly the "bit-fiddly" cost the parent task anticipated.

## The host-zstd path is also blocked

A real host-`zstd --train --dict ... -D dict file -o frame.zst` round-trip
would natively emit Compressed_Blocks that exercise the seeding
mechanism (host zstd at default settings DOES emit Repeat_Mode for
offsets-stream when compressing against a dictionary, observed via
`xxd` of `28 b5 2f fd 25 2a 2a 75 00 00 30 ...`). However the host
dictionary itself uses **FSE-compressed Huffman weights** (header_byte
< 128), which hits
`doc/08_tracking/bug/bug_zstd_fse_huffman_weight_kraft_2026-05-01.md`:
`_zstd_parse_dictionary` errors at the HUF section before sequence-table
seeding is even reached. So the FSE Kraft bug must be fixed before host
fixtures unblock this lane end-to-end.

## Resolution paths

1. **Fix the FSE Kraft bug first**, then add a host-`zstd --train`
   round-trip fixture (uses real dict + real frame, no manual byte
   construction). This is the lowest-risk path because the fixtures
   come from a known-good encoder.
2. **Hand-construct the FSE bitstream** as outlined above. ~2-3 hours
   of focused work, separate from FSE Kraft fix.
3. **Add an in-tree Compressed_Block emitter** (`zstd_compress_frame`
   currently only emits Raw or RLE blocks per `_zstd_all_same`
   detection, see `src/lib/common/compress/zstd.spl:95-160`). A
   roundtrip via `zstd_compress_frame_with_dictionary(...)` ->
   `zstd_decompress_frame_with_dictionary(...)` would prove both
   sides simultaneously, but requires implementing the encoder side
   first — a much larger scope.

Path 1 is recommended. Path 2 is a viable narrower follow-up if FSE
Kraft remains open. Path 3 is a separate lane.

## Acceptance criterion when this is fixed

Add at least one end-to-end test in `zstd_dictionary_spec.spl` (or a
sibling) that:

- Uses a dictionary whose FSE tables differ from the predefined
  distributions.
- Constructs a frame with `mode_byte` having at least one Repeat_Mode
  stream and `sequence_count >= 1`.
- Decodes successfully when the dictionary is supplied, AND fails
  with a typed error when the dictionary is omitted (or a different
  dictionary is supplied).
- Asserts on at least one decoded output byte that originated from
  the dictionary's `content_prefix` window via repeat-offset reuse.
