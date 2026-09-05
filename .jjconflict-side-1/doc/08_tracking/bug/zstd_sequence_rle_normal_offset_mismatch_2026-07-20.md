# ZSTD sequence-decode: "normal offset" test decodes as a straight back-reference copy instead of expected RLE-style expansion

**Date:** 2026-07-20
**Severity:** low (single test-vector mismatch, sibling offset-1/rep1 tests
in the same file pass)
**Status:** open — needs ZSTD-format domain expertise to determine which
side (test vector or decoder) is correct; not attempted here (out of
test-triage scope, not a mechanical fix)
**Found by:** whole-suite `test/unit/` triage campaign, `lib/common` cluster

## Symptom

`test/unit/lib/common/zstd_sequence_rle_spec.spl`, `"decodes a one-sequence
block with a normal offset"` (1 of 6 examples; the other 5, including two
adjacent offset-1/rep1 tests, pass):

```
expected [97, 98, 99, 97, 98, 99] to equal [97, 98, 99, 99, 99, 99]
```

i.e. actual decoded bytes are `"abcabc"`, expected is `"abcccc"`.

## Minimal repro

```simple
val frame = _zstd_frame(6, _compressed_block(true, [
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8,
    0x54u8,
    0x03u8, 0x02u8, 0x00u8,
    0x06u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)   # passes
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x63u8, 0x63u8, 0x63u8])  # fails
```

## Analysis (not root-caused, flagging the ambiguity)

The actual decoded output (`"abcabc"`) is consistent with a plain
non-overlapping back-reference copy (3 literal bytes `"abc"`, then a match
of length 3 at offset 3 — copy the previous 3 bytes verbatim). The
*expected* value (`"abcccc"`) looks like RLE/offset-1 expansion (repeat the
single last byte). But the test's own name/intent ("a normal offset", as
distinct from the sibling "offset one" and "rep1" tests a few lines below,
which pass) suggests it is deliberately testing the non-offset-1 case — so
either:
1. The decoder has a genuine bug specific to this raw byte encoding
   (`[0x03, 0x02, 0x00]` sequence-code bytes) where it's resolving to the
   wrong offset/match-length despite the "normal offset" framing, or
2. The test's expected byte array is simply wrong (copy-paste from the
   RLE/offset-1 sibling test case a few lines below, which does expect
   repeated-byte output).

Distinguishing these requires manually decoding ZSTD's FSE-coded
offset/match-length/literal-length sequence tables for the raw bytes above
— out of scope for a mechanical test-triage pass. Not fixed either
direction (fixing the expected array without being sure would risk
weakening/hiding a genuine decoder bug; touching the decoder source is out
of the assigned test-cluster scope regardless).

## Affected

- `test/unit/lib/common/zstd_sequence_rle_spec.spl` — 1 of 6 examples.
