# zstd and brotli encoders are container writers only — they never compress

**Status (2026-08-17, revised): zstd FIXED — `zstd_compress_frame` now emits
real Huffman-coded Compressed_Blocks. brotli STILL-OPEN.**

**Found:** 2026-08-17, lane W11-B of `.spipe/simple_enterprise_suite`, while
determining whether `test/01_unit/lib/nogc_async_mut/http_server/compression_spec.spl`
or `src/lib/nogc_async_mut/http_server/compression.spl` was wrong.

## Symptom

Measured directly, on 300 bytes of highly repetitive ASCII (`"abcdefghij"` x 30),
via the response-compression dispatcher's own entry point:

| codec | output bytes | round-trips via `decompress_bytes` auto-detect |
|-------|--------------|-----------------------------------------------|
| br      | **304** (larger than input) | no |
| gzip    | 42  | yes |
| deflate | 28  | no (raw deflate has no magic; auto-detect limitation, not a codec fault) |
| zstd    | **310** (larger than input) | yes |
| lz4     | 36  | yes |

## Cause

`src/lib/common/compress/zstd.spl` `zstd_compress_frame` is documented in its own
body as emitting "RLE block if all bytes are identical, raw block otherwise" —
it writes a valid zstd *container* around the untouched input. It therefore
always expands by the frame-header overhead. `brotli_compress` behaves the same
way in practice (300 -> 304). Both decoders are real; only the encoders are stubs.

This is a real capability gap, not a spec problem. It is recorded here rather
than absorbed into a spec expectation, per `.claude/rules/code-style.md`.

## Consequence that WAS a live defect (fixed 2026-08-17)

`compress_response_for` negotiated exactly one codec — the highest
server-preference codec the client accepted — and, when the size guard
correctly refused its non-shrinking output, returned the response uncompressed
with no attempt at the next acceptable codec. A client sending
`Accept-Encoding: zstd, lz4` therefore received a **fully uncompressed** 300-byte
body, even though it also offered lz4, which compresses the same body to 36
bytes. Fixed by walking the server preference order and taking the first
mutually-acceptable codec that actually shrinks the body; preference order is
otherwise unchanged (`Accept-Encoding: gzip, lz4` still selects gzip).

## Triage 2026-08-17 — encoders DEFERRED, no live defect remains

**Superseded for zstd by the section below.** This triage assumed a real zstd
encoder required FSE + Huffman entropy coding from scratch. That was wrong on
the facts: a Huffman literals encoder and a direct weight-header writer were
already in the tree, and a Compressed_Block with `Number_of_Sequences = 0`
needs no FSE at all. The deferral stands only for brotli.

Re-verified 2026-08-17: `compression_spec.spl` is green (20/20) including the
multi-codec fallback fixed above, so nothing user-visible is broken — the
dispatcher never serves a non-shrinking zstd/br body. Implementing real
encoders means FSE + Huffman entropy coding (zstd, RFC 8878 §4) and brotli's
static-dictionary/context modeling (RFC 7932) — a multi-week feature, not a
bug fix, and no C-runtime `libzstd`/`libbrotli` binding exists in-tree to
shortcut it. Deferred as a capability gap; the items below remain the frontier.

## 2026-08-17 — zstd FIXED (real Huffman compression), brotli STILL-OPEN

Binary identity for every measurement below:

```
$ readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
59537240 2026-08-17 12:58:51.339525019 +0000
```

(This binary self-identifies as the Rust bootstrap seed: "WARNING: this
Rust-built Simple binary is a bootstrap seed only". No pure-Simple binary is
deployed in this worktree; the module also drops to the interpreter on an
unrelated `ZstdFrameHeader.dict_id` HIR-lowering error, so all numbers below
are interpreter-executed.)

### Reproduction of the recorded symptom (before the fix)

`bin/simple run <scratch>/repro.spl` on `"abcdefghij"` x 30:

```
input 300
zstd 310
```

310 > 300 — reproduced exactly as recorded. (The brotli half of the repro
could not be measured on this binary: `brotli_compress` aborts with
`semantic: invalid assignment: cannot index assign value of type array`
inside `_slice`'s `rt_bytes_alloc` buffer, an interpreter defect unrelated to
compression ratio.)

### Root cause found

Not "a full encoder is a multi-week feature" — the encoder primitives were
already in-tree and simply unreachable:

1. `_zstd_huf_assign_weights` (`src/lib/common/compress/zstd_huf.spl`) used a
   linear weight-spreading heuristic that could not reach Zstd's Kraft
   equality `sum(2^(w-1)) == 2^depth` for most alphabets. Ten equiprobable
   symbols returned `UnsupportedFeature("zstd huf encoder weight balancing
   did not converge")`, so **every** compressed-literals path was dead.
2. There was no encoder for the real wire bit-layout. `zstd_huf_encode_literals`
   targets the LSB `ZstdBackwardBits` reader, but a Compressed_Literals_Block
   is decoded by `_zstd_decode_huffman_stream_msb` (backward MSB-first, RFC
   8478 Annex A). Feeding the LSB encoder's output to the type-2 parser fails
   with `zstd Huffman literal stream has trailing bits`.
3. `zstd_compress_frame` never attempted a Compressed_Block at all.

### Fix (3 edits, no new files, no C runtime touched)

- `src/lib/common/compress/zstd_huf.spl`: `_zstd_huf_assign_weights` now
  derives lengths from a real Huffman tree (`_zstd_huf_code_lengths`, new,
  with an 11-bit depth clamp and Kraft repair) and sets
  `weight = max_bits + 1 - len`. A complete Huffman code satisfies Kraft
  equality by construction, so convergence is no longer a heuristic.
- `src/lib/common/compress/zstd_huf.spl`: new `zstd_huf_encode_literals_msb`
  emitting the real backward MSB-first layout (zero padding, `1` marker,
  then codes MSB-first). The old LSB encoder is left untouched for its
  existing callers/specs.
- `src/lib/common/compress/zstd.spl`: `zstd_compress_frame` now splits the
  payload into <=1023-byte blocks (the Size_Format-0 single-stream limit) and
  emits each as a Compressed_Block (compressed literals + `Number_of_Sequences
  = 0`) when that is smaller, else RLE when the chunk is uniform, else raw.
  An all-same input still emits one 4-byte RLE block for the whole frame.

### Evidence after the fix

`bin/simple run <scratch>/rt.spl` (compress then `zstd_decompress_frame`,
byte-comparing the result):

```
repetitive300: in=300 out=196 roundtrip=true
empty: in=0 out=9 roundtrip=true
one: in=1 out=10 roundtrip=true
allsame5000: in=5000 out=11 roundtrip=true
pseudorandom3000: in=3000 out=3016 roundtrip=true
text2700: in=2700 out=1721 roundtrip=true
```

The recorded 300 -> 310 case is now 300 -> 196, and English text compresses
2700 -> 1721. Incompressible input still expands, by the 3-byte-per-block
raw-block header only (3000 -> 3016). Every case round-trips byte-exactly
through the in-tree RFC 8478 decoder.

Regression check on the changed `_zstd_huf_assign_weights`, exercising the
five inputs asserted by `test/01_unit/lib/common/zstd_huf_round_trip_spec.spl`
through the same three calls that spec makes (`zstd_huf_encode_literals` ->
`zstd_huf_build_table_for_test` -> `zstd_huf_decode_stream_for_test`), via
`bin/simple run <scratch>/hufrt.spl`:

```
one-symbol: roundtrip=true
two-symbol: roundtrip=true
4-symbol mixed: roundtrip=true
skewed a8b4c2d1: roundtrip=true
skewed A16B4C2D1: roundtrip=true
```

**Not verified: `bin/simple test` spec runs.** `bin/simple test
test/01_unit/lib/common/zstd_huf_round_trip_spec.spl` was started and killed
after **14 minutes of wall time having produced no output at all** (1m17s of
CPU; the box was carrying 6 other sessions' native-build workers at the time).
Four further specs queued behind it never started. Per
`.claude/rules/testing.md` an absent results line is INCONCLUSIVE, not green,
so no spec verdict is claimed here — the evidence above is the direct
`bin/simple run` repro that rule prescribes instead.

No file under `src/runtime/*.c` was touched, so
`check-c-runtime-compiles-push.shs` is not applicable to this change.

### Why brotli is NOT fixed

`brotli_encode` already has two real compressing paths, but both are gated on
a *simple* prefix code, which brotli caps at 4 symbols: `_try_encode_literal_only`
refuses more than 4 distinct bytes, and `_try_encode_lz77` additionally needs
the whole suffix to be one backreference with a prefix of at most 7 literals.
The recorded 300-byte fixture has 10 distinct bytes and a 10-byte prefix, so
both refuse and the uncompressed meta-block wins. Lifting either gate needs a
*complex* (canonical, code-length-coded) prefix-code writer in
`src/lib/nogc_sync_mut/compression/brotli/encoder.spl` — genuinely new
machinery, unlike zstd where the primitives already existed. Left STILL-OPEN
rather than faked.

## Still open

- `brotli_compress` performs no actual compression for inputs with more than
  4 distinct byte values (needs a complex prefix-code writer).
- zstd compressed blocks are capped at 1023 bytes each (single-stream
  Size_Format 0) and need the symbol alphabet's highest byte to be < 129 for
  the direct weight header; larger/binary chunks fall back to raw blocks.
  4-stream literals and an FSE weight header would lift both.
- zstd emits no sequences (no LZ77 match coding) — literals-only entropy
  compression. Match coding needs the interleaved predefined-FSE sequence
  bitstream.
- `decompress_bytes(_, nil)` auto-detect cannot recognise a raw deflate stream
  (no magic bytes). Callers must pass the codec hint for deflate.

Until the encoders are implemented, `supported_encodings()` legitimately lists
zstd and br — the dispatcher will simply never select them for a body they
cannot shrink.
