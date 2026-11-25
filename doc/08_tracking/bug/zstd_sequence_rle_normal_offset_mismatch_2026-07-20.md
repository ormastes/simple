# ZSTD sequence-decode: "normal offset" test decodes as a straight back-reference copy instead of expected RLE-style expansion
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Resolution — 2026-11-25 (CLOSED: test vector was wrong, decoder is correct)

**Verdict:** the TEST VECTOR was wrong. The Simple decoder's normal-offset
sequence resolution is correct. No decoder change was needed.

### Reference-decoder evidence

Tool: python `zstandard` 0.25.0 (libzstd bindings), installed via
`pip install --user zstandard` on the triage host. The exact 10-byte block
payload from the spec (`18 61 62 63 01 54 03 02 00 06`) was wrapped in a
valid frame (explicit window descriptor, no FCS — see caveat below) and
decoded by libzstd:

```
$ python -c '... ZstdDecompressor().decompress(frameB)'
B OK -> [97, 98, 99, 97, 98, 99]        # "abcabc"
```

Hand-decode per RFC 8878 agrees: literals header `0x18` = raw, 3 literals
("abc"); 1 sequence; modes byte `0x54` = LL/OF/ML all RLE with codes
`03/02/00` -> LL=3 (code 3, 0 extra bits), offset code 2 -> 2 extra bits
from bitstream `0x06` (sentinel at bit 2, payload bits "10" = 2) giving
offset value 4+2=6 -> real offset 6-3=3, ML code 0 -> ML=3. Copy 3 bytes
from offset 3 -> "abcabc". The old expected value "abcccc" describes an
offset-1 expansion, which contradicts the frame's own offset code — it was
a copy-paste from the offset-1 sibling test, as the original analysis
suspected (option 2).

### What changed and when

- The wrong vector (`...0x63u8, 0x63u8, 0x63u8]` = "abcccc") existed only in
  the legacy copy `test/unit/lib/common/zstd_sequence_rle_spec.spl`. That
  copy was dropped by commit `b214ccc5a02` ("test: consolidate
  test/unit/lib -> test/01_unit/lib"), whose migrated
  `test/01_unit/lib/common/zstd_sequence_rle_spec.spl` already carries the
  corrected expectation `[0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]`
  ("abcabc").
- 2026-11-25: added a comment at the assertion in
  `test/01_unit/lib/common/zstd_sequence_rle_spec.spl` citing this
  reference-decoder evidence, so the vector is not "fixed" back.

### Spec results

- Before (branch `work/p3-zstd-20261125`, pre-comment):
  `SIMPLE_LIB=src bin/simple.exe test test/01_unit/lib/common/zstd_sequence_rle_spec.spl --mode=interpreter`
  -> 6 total, 6 passed, 0 failed (the reported failure no longer reproduces;
  the migrated spec already had the corrected vector).
- After (comment added): re-run, 6/6 PASS (comment-only change).

### Caveat (not this bug, no action taken)

The spec's hand-rolled frame declares a single-segment window of 6 bytes
while the compressed block is 10 bytes; strict libzstd rejects that frame
("Src size is incorrect") because a compressed block may not exceed
Block_Maximum_Size = min(window, 128K). The Simple decoder is lenient here
and decodes the block anyway. That leniency is a separate, cosmetic
strictness gap (the decoder never produces wrong bytes for it) and was left
untouched; the reference-verified payload decode above used a
spec-compliant window to establish the wire truth.
