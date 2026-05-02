# Zstd HUF decoder strict `remaining != 0` invariant — incompatible with mixed-length encoder

**Status:** OPEN. Identified 2026-05-02 by W12-E end-to-end trace.
**Severity:** blocks RFC-8478 compliant Zstd Huffman literal encoder from round-tripping through the existing pure-Simple decoder.
**Path:** `bug` track. Decoder-side fix; W9-C encoder primitives are dead-on-shelf until this lands.

## Symptom

W9-C landed Zstd Huffman literal encoder primitives (`zstd_huf_encode_literals`) that pass structural unit tests but FAIL discriminating round-trip through the existing pure-Simple decoder `_zstd_decode_huffman_stream`.

W12-E disproved the W9-C "bit-direction mismatch" framing (Brotli-precedent analogy). End-to-end trace:
- Decoder fills `slot = reverse(code,bits) | (suffix << bits)` in `zstd_huf_expand_decode_table`
- Encoder emits `reverse(code,bits)` LSB-first via `zstd_bit_writer_append_lsb`
- Compositions match. Bit-direction is consistent.

## Root cause (one of two, this is the HUF half)

`src/lib/common/compress/zstd.spl:896` — `_zstd_decode_huffman_stream` enforces:

```spl
if zstd_bits_remaining(reader) != 0 { return Err(...) }
```

at end-of-stream. Combined with the windowed `peek(table_bits) ; consume(entry.bits)` decoding loop, this strict invariant is **mathematically incompatible** with any RFC-8478 Huffman encoder for mixed-length alphabets (i.e., where different symbols have different code lengths):

- **Pre-padding** (low-reservoir position, decoded-LAST): the trailing pad bits leak into the strict `remaining == 0` check at end-of-stream. The decoder reads the actual data correctly, then errors on pad-bit residue.
- **Post-padding** (high-reservoir position, decoded-FIRST): the `peek(table_bits)` of the first iteration reads window-bits that include pad bits, corrupting the first decoded codeword.

There is **no encoder-only fix**. Any encoder that produces a valid HUF stream per RFC 8478 will trip one of these two failure modes given the current decoder.

## Strict-check provenance

Added by commit `88b3b82722`. Predates W9-C work. The strict check appears to be over-conservative beyond what RFC 8478 §4.2.1 mandates — the spec says streams end on a 1-bit terminator, but the decoder's exact byte-position check goes further.

## Affected encoders

- **W9-C `zstd_huf_encode_literals`** (`src/lib/common/compress/zstd_huf.spl`) — deferred from end-to-end test for this reason.
- Any future RFC-8478-compliant Huffman literal encoder.

## Affected decoded streams (currently passing)

The decoder works correctly for streams that happen to end with no pad bits — most reference test vectors crafted for the existing pure-Simple decoder path. Production zstd output uses encoders that produce pad bits (per RFC 8478 §4.2.1), so this is a real interop gap.

## Fix

Replace strict `remaining != 0` check with RFC 8478 §4.2.1 sentinel-bit termination logic:

1. Decoder reads up to but not past the 1-bit terminator marker.
2. End-of-stream condition: pad-byte ends with `1` followed by zero or more `0`s — count the trailing zeros + leading 1 bit, and consider the stream consumed at that point.
3. Allow the consumed-bit count to exceed exact byte boundary as long as the terminator was honored.

Reference: RFC 8478 §4.2.1.5 "Huffman-Coded Streams"; the four-stream variant uses a 1-bit-then-zeros padding to align to byte boundary.

## Verification

After fix:
- Round-trip W9-C `zstd_huf_encode_literals` output through `_zstd_decode_huffman_stream` byte-exact.
- Cross-check against `zstd` CLI output (commit a small fixture per `scripts/`)
- Existing decoder specs continue to PASS (no regression).

## Out of scope

- The orthogonal FSE encoder bug at `zstd_fse.spl:415` (filed separately at `bug_zstd_huf_literal_encoder_bit_layout_2026-05-02.md` § revised hypothesis).
- W9-C façade level relax {3}→{1,2,3} — verified by W12-E to NOT route through this encoder, no regression.

## Cross-references

- `doc/08_tracking/bug/bug_zstd_huf_literal_encoder_bit_layout_2026-05-02.md` § revised hypothesis (W12-E investigation).
- W12-E commit `7a2d261b50c1` doc(zstd): revise W9-C bug-doc hypothesis after end-to-end trace.
- W9-C commits at `d7e46403c2`, `a248ebff0a`, `0dcf6c357c`, `afad9a3907`, `9516e68fa7`, `1e98028811`.
- `src/lib/common/compress/zstd.spl:896` (strict check).
- `src/lib/common/compress/zstd_huf.spl` (encoder primitives).
- RFC 8478 §4.2.1.5.
