# `RAW_RGBA_MAGIC` constant value does not match its documented 'RBPA' byte pattern

Date: 2026-09-06
Status: open
Severity: P4 (test-only codec, no production callers affected beyond snapshot tests)
Location: `src/lib/skia/feature/codec/raw_rgba.spl:14-16`

## Symptom

`test/01_unit/lib/skia/raw_rgba_spec.spl` scenario "encode_raw_rgba: header is
16 bytes with correct magic" fails on the third magic byte:

```
expected 81 to equal 80
```

Verified as a legitimate, pre-existing RED (reproduces identically on
`git show HEAD:test/01_unit/lib/skia/raw_rgba_spec.spl` before this session's
modernization edit) -- 5 of 6 scenarios in the file pass; this one scenario
fails both before and after.

## Root cause

`src/lib/skia/feature/codec/raw_rgba.spl` declares:

```simple
# Magic marker: bytes 'R','B','P','A' = 0x52 0x42 0x50 0x41 big-endian u32.
# = 0x52425041 = 1380012353
const RAW_RGBA_MAGIC: i64 = 1380012353
```

The comment's own hex-to-decimal conversion is wrong: `0x52425041` is
**1380077633**, not `1380012353`. Decoding `1380012353` byte-by-byte
(big-endian) gives `0x52 0x41 0x51 0x41` = ASCII `'R','A','Q','A'`, not the
documented `'R','B','P','A'`. The magic tag actually written into every
encoded blob's header (and read back by the decoder, which round-trips
correctly since encode and decode both use the same wrong constant) is
`RAQA`, not `RBPA`.

Confirmed independently in isolation (no dependency on the codec or any
interpreter defect):

```simple
val v: i64 = 1380012353
expect((v >> 24) & 0xFF).to_equal(0x52)  # 82 'R' -- passes
expect((v >> 16) & 0xFF).to_equal(0x42)  # fails: actual 65 'A', not 66 'B'
expect((v >> 8)  & 0xFF).to_equal(0x50)  # fails: actual 81 'Q', not 80 'P'
expect(v & 0xFF).to_equal(0x41)          # 65 'A' -- passes
```

## Impact

None in practice: `decode_raw_rgba` reads back the same wrong constant it
was encoded with, so round-tripping (the codec's only real contract) is
unaffected -- the round-trip scenario in the same spec file passes. The only
externally-visible effect is that the shipped magic bytes are not the ASCII
tag the source comments claim, which would surprise anyone inspecting a
`.rawrgba` blob by hand expecting `RBPA`.

## Fix

Change `src/lib/skia/feature/codec/raw_rgba.spl:16` to
`const RAW_RGBA_MAGIC: i64 = 1380077633` (== `0x52425041`), matching the
documented comment. This is a one-line source change outside this session's
assigned scope (`test/01_unit/lib/skia/raw_rgba_spec.spl` only); left for the
owning session/agent. The spec's magic-byte scenario is intentionally left
RED (not weakened) to keep documenting the real, pinned wire format until
the constant is corrected -- see the `# NOTE:` comment at the scenario site.

## Related

None found in `doc/08_tracking/bug/` prior to this record (checked via
`grep -rl "raw_rgba\|write_u32_be\|RBPA"`).
