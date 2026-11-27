# LZ4 auto-frame round-trip rejects its own empty-payload output as corrupt

- **Status:** RESOLVED (2026-11-25 — empty-input round-trip verified working at release/1.0.0 tip; see fleet verification note at bottom)
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

## Fleet verification note (2026-11-25, worktree wt-p2w1-ae, branch work/p2w1-ae-20261125)

STALE — the defect no longer reproduces at `origin/release/1.0.0` HEAD
(`38265c7f249`). Verified by executing the doc's own minimal repro under the
tracked seed binary (`SIMPLE_LIB=src bin/simple.exe run`, Windows host):

- Empty round-trip (the exact repro from this doc):
  `compress_bytes([], lz4 options)` → `decompress_bytes(...)` prints
  `is_err=false`, `roundtrip_len=0`. The `CorruptStream(lz4 empty data
  block)` failure is gone.
- Non-empty control (1000-byte payload): round-trips intact
  (`nonempty_roundtrip_ok=true`).
- The corruption guard is still intact: a hand-crafted frame whose data block
  is zero-length *uncompressed* (`size_word = 0x80000000`, i.e. not the end
  mark) is still rejected (`zero_len_block_rejected=true`) by the guard at
  `src/lib/common/compress/lz4.spl:336-338`.

Root cause of the stale row: the encoder side of the either/or fix this doc
proposed has landed. `lz4_compress_frame`
(`src/lib/common/compress/lz4.spl:195-228`) emits data blocks only inside
`while pos < data.len()`, so empty input produces the canonical frame —
descriptor + immediate end mark, no data block record (docstring: "Empty
input uses the canonical immediate end mark"). The decoder's end-mark path
(`lz4.spl:315-331`) accepts that shape, so encoder and decoder agree again.

The named harness spec moved to
`test/01_unit/lib/common/compress_facade_harness_spec.spl` (still asserts the
empty-fixture round-trip, unweakened). It could not be executed on this host:
every `bin/simple.exe test` invocation at HEAD fails in the test runner
itself with `unknown decorator '@representation_boundary'` (pinned Rust seed
v1.0.0-rc.1 predates commit `cfd89933699`) — the known repo-wide
source/binary inconsistency, unrelated to this bug. The executed repro probes
above cover the same behavior the spec's first fixture asserts.

Status flipped OPEN → RESOLVED. No code change in this lane.
