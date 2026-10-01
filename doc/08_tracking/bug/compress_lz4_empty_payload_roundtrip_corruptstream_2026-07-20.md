# LZ4 auto-frame round-trip rejects its own empty-payload output as corrupt

- **Status:** OPEN
- **Discovered:** 2026-07-20, whole-suite triage campaign
- **Area:** `src/lib/common/compress/lz4.spl` — LZ4 frame encoder/decoder facade
- **Severity:** Medium — breaks the empty-input round-trip for the public
  `compress_bytes`/`decompress_bytes` facade (and the `lz4_*_frame_for_tier`
  variants) whenever the payload length is 0.

## Symptom

`test/unit/lib/common/compress_facade_harness_spec.spl`, example
"round-trips deterministic framed fixtures across every public codec", fails
on the very first fixture (`_fixture_empty() -> []`) with:

```
semantic: called unwrap on Err: CompressionError::CorruptStream(lz4 empty data block)
```

## Minimal repro

```spl
use std.common.compress.{CompressionCodec, default_compression_options, compress_bytes, decompress_bytes}

fn main():
    val payload: [u8] = []
    val options = default_compression_options(CompressionCodec.lz4)
    val encoded = compress_bytes(payload, options)
    val decoded = decompress_bytes(encoded, nil)
    print(decoded.is_err())   # prints true — should be false

main()
```

## Root-cause hypothesis

`src/lib/common/compress/lz4.spl` around line 394-396 explicitly rejects any
zero-length data block on decode:

```
# Reject empty data blocks (zero payload with high bit set or not)
...
    return Err(CompressionError.CorruptStream("lz4 empty data block"))
```

This appears to be a deliberate anti-corruption guard for the *general* LZ4
frame format (a zero-size block inside a stream usually does indicate
truncation/corruption for non-empty inputs). However the LZ4 **encoder** path
(same file) emits exactly this shape — a single zero-length data block — when
asked to compress a 0-byte payload, since there is no literal/match data to
emit. The encoder and decoder therefore disagree on whether a lone
zero-length data block is valid: the encoder produces it as the correct
representation of "empty input", the decoder treats it unconditionally as
corruption.

The fix is almost certainly on the decode side: the empty-data-block guard at
line ~394-396 needs to allow a zero-length block specifically when it is the
frame's *only* block (i.e., immediately followed by the end-mark), while
still rejecting a zero-length block that appears after literal blocks or
whose presence is inconsistent with a non-zero declared content size — OR the
encoder needs to special-case empty input to skip emitting a data block at
all (frame descriptor + immediate end-mark, no block record). Either fix
needs to be paired with the other side reviewed for the corresponding
behavior. Not attempted here — out of scope for a spec-only triage pass (this
is a `src/lib` runtime defect, not a stale test).

## Failing command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/common/compress_facade_harness_spec.spl --no-session-daemon
```

## Note

The spec's assertion (`expect(decoded.unwrap()).to_equal(payload)` /
`expect(decoded.is_err()).to_equal(false)`) is correct and must NOT be
weakened or dropped — round-tripping an empty payload through a compression
codec is a legitimate requirement. This is a genuine codec defect, not a
stale test.
