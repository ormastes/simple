# Cross-module ByteSpan misreads small heap-built [u8] arrays (deployed interpreter)

**Filed:** 2026-07-19 · **Status:** OPEN · **Area:** interpreter / cross-module struct fields
**Found via:** every PNG chunk CRC from `png_encode.spl` was wrong while its
zlib stream was byte-perfect.

## Symptom
`ByteSpan.get(i)` (imported from `std.common.bytes.span`) returns garbage when
the span wraps a SMALL heap-built `[u8]` (from `text.bytes()` or built by
`push()`), called from another module on the deployed self-hosted interpreter:

- `ByteSpan.new("IEND".bytes()).get(0..3)` → 72,2,0,0 (expect 73,69,78,68)
- pushed-then-copied 4-elem array → 72,40,112,32 (different garbage)
- LITERAL array `[73u8,69u8,78u8,68u8]` → correct
- LARGE pushed arrays appear correct (the 1.5MB scanline buffer fed through
  `deflate_stored(ByteSpan.new(data))` + `Adler32.update(span)` produced a
  zlib stream python's zlib decompressed with matching Adler)
- A byte-identical LOCAL replica of the ByteSpan struct+impl in the calling
  file works correctly → defect is specific to the IMPORTED struct
  (cross-module field poison class, cf.
  project_seed_crossmodule_field_option_poison_2026-06-14)

Repro pattern (recreate as build/tmp probes): imported
`ByteSpan.new("IEND".bytes())` + `Crc32.update(span)` → crc_raw=2086697888
(0x7C607BA0); expected 2923585666 (0xAE426082). Local byte-identical
LocalSpan replica in the same file → correct. Free functions over flat
arrays (`gzip_crc32`, `adler32`) → correct.

## Impact
Any cross-module consumer of ByteSpan/Crc32/Adler32 over small dynamic
arrays computes garbage: png_encode chunk CRCs (fixed by workaround),
potentially other checksum/wire users — audit `grep -rl 'ByteSpan.new'
src/lib` for small-array call sites.

## Workaround (documented safe shape)
Pass flat `[u8]` to free functions (e.g. `gzip_crc32(data)`,
`adler32(data)`) instead of storing the array in an imported struct's field.
Applied in `png_encode.spl:_chunk/_zlib_store` (verified: 4x4 test PNG now
has all chunk CRCs valid per python zlib oracle).

## Hypothesis
Small arrays use an inline/SSO representation that does not survive being
stored into an imported struct's field (representation tag lost or pointer
into a moved temporary); large arrays are heap-normalized and survive.
