# Zstd FSE-compressed Huffman-weight decode: Kraft sum failure on real fixtures

Date: 2026-05-01
Status: **FIXED 2026-05-01 -- root cause: `ZstdBackwardBits` reads bits LSB-first
within each byte, but RFC 8478 Annex A mandates MSB-first for the FSE state
bitstream; Huffman literal decode masked the bug via `zstd_huf_reverse_bits`
table compensation while the FSE state machine had no compensation. Fixed by
adding a dedicated MSB-first backward bit reader (`ZstdMsbBackwardBits` in
`src/lib/common/compress/zstd_bits.spl`) used only by
`_zstd_parse_fse_compressed_weights`, plus a Kraft-sum-derived `max_bits` in
`zstd_huf_weights_to_symbols` (the previous max_weight-based derivation
silently mis-categorised weights when no symbol had the longest codeword
length, producing spurious "oversubscribed" rejects on the corrected weight
sets). 6/6 PASS in `test/unit/lib/common/zstd_fse_weights_spec.spl`,
including byte-exact decode of FX1 -> 123 weights/sum 128=2^7 and a fresh
host-zstd fixture FX_HOST_FRESH -> 123 weights/sum 256=2^8.**
Source: discovered while writing `test/unit/lib/common/zstd_fse_weights_spec.spl`
to discharge `verify_common_compression_framework.md` line 13 (FAIL on
`src/lib/common/compress/zstd.spl:704` -- "verification still cannot claim
support for the missing FSE-compressed Huffman-weight path").

## Symptoms

`_zstd_parse_fse_compressed_weights` (and its public alias
`zstd_parse_fse_huffman_weights`, added 2026-05-01 as a test seam at
`src/lib/common/compress/zstd.spl:828`) returns
`CompressionError.CorruptStream("zstd huf final weight cannot complete a
power-of-two tree")` on **every** real-world FSE-Huffman-weight description
extracted verbatim from host `zstd -1`/`zstd -3` output -- including five
distinct fixtures of size 17-22 bytes covering different English-prose
payloads (alphabet sizes 28-32 symbols).

The dispatch at `_zstd_parse_direct_weights` (line 833 of `zstd.spl`)
correctly routes `header_byte < 128` to the FSE path, and
`zstd_fse_parse_normalized_counts` + `zstd_fse_build_decode_table` accept
the data, but the back-stream weight decode loop at lines 763-822 produces
a weight set whose `zstd_huf_complete_weights` rejects -- meaning
`sum(2^(weight-1))` over decoded weights never reaches a value whose
power-of-two completion equals a single `2^k` term (the RFC 8478 §4.2.1.1
"completing to nearest power of 2" requirement).

## Reproduce

`test/unit/lib/common/zstd_fse_weights_spec.spl` contains five FSE
Huffman-tree blobs `FX0..FX4` extracted from host-`zstd` output. All five
fail the happy-path `zstd_parse_fse_huffman_weights(...)` call with the
same error. The spec currently pins this buggy behaviour explicitly so it
will fail loudly when the bug is fixed.

```spl
use std.common.compress.zstd.{zstd_parse_fse_huffman_weights}

val FX1: [u8] = [
    0x15u8, 0x80u8, 0x25u8, 0x3Bu8, 0xF0u8, 0xDBu8, 0xADu8, 0x45u8,
    0x88u8, 0x76u8, 0x98u8, 0x7Eu8, 0x22u8, 0x35u8, 0x32u8, 0x41u8,
    0x93u8, 0x10u8, 0x2Bu8, 0x07u8, 0xF3u8, 0xD2u8
]
# returns Err(CompressionError.CorruptStream("zstd huf final weight cannot
# complete a power-of-two tree")) -- buggy.
```

## Reference (independent Python decoder) gives a valid answer

A Python port of the RFC 8478 §4.1.1 + §4.2.1.1 decoder, verified against
the host `zstd -d` output on the same source frame, decodes FX1 to a 145-
entry weight vector with `partial_sum = 192` and last weight 7
(completing to `2^8`, which is RFC-valid: `Max_Number_of_Bits = 8 <= 11`).

So **a correct decoder accepts these bytes**; the Simple decoder is
emitting a wrong weight set.

## Suspected divergences (not investigated to root cause)

1. **`zstd_fse_parse_normalized_counts` may over-emit a trailing zero.**
   On FX1 the Simple decoder reports `counts.len = 6`, the Python
   reference reports `counts.len = 5` (counts `[23, 0, 0, 5, 4]`). One
   extra zero at the tail would not change the FSE table mapping but
   could change the decoded symbol stream when the FSE decoder hits the
   "less than one" symbols at the high end of the table. Worth checking
   the loop terminator at `src/lib/common/compress/zstd_fse.spl:110`.

2. **`_zstd_read_bits_zero_padded` may shift partial bits the wrong way.**
   When `remaining < count`, the helper returns `partial_res.unwrap().0`
   directly, without left-shifting by `(count - remaining)`. The zstd C
   reference (`bitstream.h::BIT_lookBits`) returns the partial bits in
   the **high** bit positions of the requested field with zeros at the
   low end (so a baseline + low_bits arithmetic still picks the right
   table cell). The Simple version returns them in the **low** bit
   positions. See `src/lib/common/compress/zstd.spl:716-731`.

3. **Pad/break alternation may emit one too many or too few weights.**
   The canonical zstd FSE tail loop emits `state1`'s symbol, checks
   `BIT_reloadDStream==overflow`, and if overflow emits `state2`'s
   symbol then breaks. The Simple loop emits `state1`'s symbol, advances
   `state1` (zero-padded), checks the padded flag, and on padded emits
   `get_entry(state2)` -- but `state2` has not been advanced this
   iteration, so this may be one symbol behind the reference depending
   on which side of the advance the overflow check straddles.

A small reproduction harness in `/tmp/build_zstd_fse_fixture.py` (kept
locally, not committed) exercises all three paths against host-zstd
output.

## Spec

`test/unit/lib/common/zstd_fse_weights_spec.spl` -- 4 negative cases
green; the happy-path `it` asserts the current buggy error message and
will fail when the bug is fixed.

## Verify report

`doc/09_report/verify_common_compression_framework.md` line 13 stays
**FAIL** with a reference to this bug doc. The implementation exists and
is dispatched correctly, but is non-functional on real data; full RFC-
conformant Huffman literal decode therefore remains unsupported even
when `header_byte < 128`.

## Out of scope for this lane

- A full FSE-state-machine fix (multi-day investigation, requires either
  a Simple-language step-debugger or a bit-exact cross-trace against
  zstd C's `FSE_decompress`).
- Re-encoding host-zstd 4-stream literals as single-stream to land an
  end-to-end `decompress_bytes` round-trip (blocked by FSE bug above
  and by the separate `zstd.spl:324` non-RLE-sequence-tables FAIL).

## Fix candidates (do not act -- guesses)

- Audit (1) above first: print `counts.counts` in compiled mode (per
  `feedback_compile_mode_false_greens.md` interpreter mode skips
  while-loop bodies in `it` blocks) and compare against the Python
  reference `[23, 0, 0, 5, 4]`.
- If counts match, audit (2): patch `_zstd_read_bits_zero_padded` to
  left-shift the partial value by `(count - remaining)` and re-test.
- If still failing, audit (3): align the break condition with the
  canonical `*op = state1.sym; if overflow: *op = state2.sym; break`
  pattern.
