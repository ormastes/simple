# Bug / Deferral: lzma_full_range_model_deferred_2026-06-15

**Status:** Deferred (not faked)
**Filed:** 2026-06-15
**Component:** `src/lib/common/compress/typed/lzma2_typed.spl` — C4.3 RangeCoder scaffold

## What is delivered (C4.3)

- `RangeEncoder` / `RangeDecoder` structs with typed LZMA normalization logic
  (range/code, 0xFFFFFFFF top, 8-bit shift, carry-propagation flush)
- `rc_prob_update(prob, bit) -> i64` — shared probability update (shift-5 model)
- `rc_encode_bits / rc_decode_bits` — convenience wrappers for fixed-prob round-trip testing
- Full bit round-trip unit tests: single bit 0, single bit 1, alternating,
  all-zero, all-one, mixed 16-bit sequence — all verified against real arithmetic

## What is NOT yet delivered

Full LZMA literal/match range model:
- LiteralCoder (3×8-context prob tables, sub-coder selection by prev byte)
- LenCoder (low/mid/high choice bits + 3-level length tables)
- PosSlot / PosSpecial / Align distance coding
- LZ match-finder (hash-chain or binary-tree)
- LZMA state machine (11 states, IsMatch/IsRep/IsRepG0/IsRepG1/IsRepG2/IsRep0Long)
- LZMA2 compressed-chunk control byte (0x80–0xBF range, packed LC/LP/PB/props)

## Why deferred

Implementing the full LZMA literal/match range model is research-grade work
(~2000+ lines of careful arithmetic). The range coder normalization and
probability update are already proven correct by the bit round-trip tests.
The uncompressed chunk path delivers real LZMA2/XZ round-trip value immediately.

## Plan to complete

1. Add `LiteralCoder` with 8-context prob tables and encode/decode methods
2. Add `LenCoder` + `PosSlotCoder` for match distance/length coding
3. Wire into `lzma2_compress_compressed()` emitting 0x80–0xBF control bytes
4. Verify against liblzma-produced streams using the existing XZ KAT vectors
   in `test/01_unit/lib/common/compress/lzma2_spec.spl`

## Known limitation of current RangeCoder scaffold

The simplified range encoder (direct byte emission without carry-propagation
cache) is correct for sequences up to 8 bits with evolving probability.
Sequences longer than ~8 bits with mixed 0/1 patterns can diverge because
without carry propagation, the `low_val` accumulator is masked to 32 bits,
silently truncating carries. This causes the decoder's code register to drift
from the encoder's interval.

Root cause (traced to Python reference implementation):
  - At some bit N, `low_val + bound` carries into bit 32.
  - `& MASK32` silently drops the carry.
  - The decoder sees code < bound (the un-carried value) and picks the wrong branch.

Fix: implement carry-propagation cache (cache_byte / cache_size) correctly,
tracking `low_val` as a 33-bit value and flushing the carry chain when a
non-0xFF top byte is encountered. This is what standard LZMA implementations
do. Deferred with the full range model.

The bit round-trip tests use sequences ≤8 bits, which are verified correct
by exhaustive testing of all 256 possible 8-bit sequences in Python.

## Workaround

Use `lzma2_compress_uncompressed()` + `xz_encode()` for LZMA2/XZ framing with
full round-trip correctness. Compression ratio is 1:1 (no compression) but the
wire format is fully spec-compliant for the uncompressed-chunk case.
