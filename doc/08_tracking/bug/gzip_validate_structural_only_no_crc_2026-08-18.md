# gzip_validate passes a corrupted stream — structural checks only, no CRC

**Status:** OPEN
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
