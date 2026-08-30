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

## Perf note on the workaround (2026-07-19)
Flat-array free functions are correct but the interpreted lane pays per-byte
call/loop overhead: `gzip_crc32`+`adler32` over png_encode's MB-scale IDAT
(1.5MB at 960x540) blew a 850s conversion budget that previously fit in
~420s with the incremental span path (which is only empirically-correct for
LARGE arrays). Practical guidance until the root ByteSpan fix: for bulk
image export prefer formats without checksums (BMP + host `sips -s format
png`; see build/tmp/ppm2bmp.spl) or keep png_encode for small images. The
ROOT fix (interpreter representation of small arrays stored into imported
struct fields) removes the dilemma.

## TRUE ROOT CAUSE (2026-07-19 agent sweep — supersedes title & hypothesis)
NOT cross-module, NOT small-array/SSO. `rt_string_bytes` (backing
`text.bytes()`) stored each byte TAGGED via `rt_value_int(b)` = `b << 3`,
while every other `[u8]` producer (literals, `push(u8)`) stores RAW bytes.
The `[u8]`-typed element read truncates the slot with `& 0xFF` WITHOUT
untagging → returns the tag's low byte (73<<3=0x248 → 0x48=72 — the exact
"72,2,0,0"). The generic/[i64]/inferred read path conditionally untags,
masking the bug everywhere except `[u8]`-typed sites (params, struct fields
like ByteSpan.data, `var x: [u8]`). Size-independent; "local replica works"
was a red herring (local test read via inferred path).

FIX (landed): store the raw byte in both runtimes —
`src/runtime/simple_core/core_string.spl:173` and
`src/runtime/runtime_native.c:1125`. UNVERIFIED-ON-DEPLOY until the next
bootstrap redeploy; verify with `build/tmp/bspan/m_localvs.spl` (expect
73,69,78,68 everywhere) and the Crc32 oracle (expect 0xAE426082 for IEND).
Pre-existing separate quirk (unchanged): `[u8]` passed to `[i64]` param
misdecodes multiples of 8. The png_encode flat-fn workaround can be
reverted after redeploy verification.
