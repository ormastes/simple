# gzip_validate passes a corrupted stream — structural checks only, no CRC

**Status:** RESOLVED (2026-08-18)
**Filed:** 2026-08-18
**Found by:** binary_domains_spec corruption test (binary SSpec goal-4 infra).

`gzip_validate` (src/lib/nogc_sync_mut/compression/gzip/compress.spl:178)
checks magic bytes, header parse, and footer parse — it never inflates or
verifies the footer CRC32/ISIZE against the payload. Measured: flipping one
byte inside the deflate body of a valid stream still returns true. The name
over-promises; callers using it as an integrity check get a false pass.

`gzip_decompress` is NOT affected — it calls `gzip_footer_validate` against
the actual decompressed bytes and returns nil on mismatch (this is the
load-bearing rejection contract, asserted in
test/01_unit/lib/common/spec/evidence/binary_domains_spec.spl).

Fix options: (a) rename to gzip_validate_structure; or (b) add a full
decode-and-CRC path (cost: full inflate). Either way the doc comment must
state what is and is not checked.

## Resolution (2026-08-18)

Chose option (b): `gzip_validate` now inflates the payload (same extraction
path as `gzip_decompress`) and delegates to `gzip_footer_validate`, which
compares the decompressed bytes' CRC32 and ISIZE (mod 2^32) against the
footer trailer, failing closed on any mismatch. Doc comment on the function
now states exactly what is checked.

Reproduce spec (fails pre-fix, confirmed with the old code restored via
`git show HEAD:<path>` before the fix, wrong-pass measured as
`Results: 6 total, 2 passed, 4 failed` including the REPRODUCE case; passes
post-fix as `Results: 6 total, 6 passed, 0 failed`):
`test/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.spl`

Also updated `test/01_unit/lib/common/spec/evidence/binary_domains_spec.spl`
to assert `gzip_validate` now rejects the corrupted stream directly (it
previously only asserted the `gzip_decompress` rejection contract as a
workaround for this gap).

All existing gzip specs remain green:
`test/01_unit/lib/common/compress/gzip_spec.spl`,
`test/01_unit/lib/common/compress/gzip_header_spec.spl`,
`test/01_unit/lib/nogc_sync_mut/compression/gzip_inflate_negative_offset_guard_spec.spl`,
`test/01_unit/lib/common/compress/compression_utilities_spec.spl`.
