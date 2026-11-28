# deflate_compress emitted a non-terminated (sync-flush) stream; unzip rejected ZIP entries

Status: verification-pending
Issue: #12291

## Symptom
`test/01_unit/lib/common/archive/deflate_compress_spec.spl` ("produces an
archive the system unzip tool accepts") failed. First because
`build/test_tmp/` did not exist on a fresh checkout; once created, `unzip -t`
reported `invalid compressed data to inflate` (exit 2).

## Root cause
`std.common.compress.deflate.deflate_compress` delegated to the sync-flush
writer (BFINAL=0 fixed block + empty stored block, `00 00 FF FF` tail). That
form is correct for RFC 7692 permessage-deflate, but it never ends the stream,
so zlib-based readers reject it inside a ZIP entry. The in-tree inflate accepts
an unterminated stream, so in-repo round trips passed and hid it.

## Fix
`deflate_compress` now emits one complete BFINAL=1 fixed-Huffman block
(`deflate_block_fixed(tokens, true)`). `deflate_compress_sync_flush` is unchanged
(the websocket permessage-deflate paths use it). The spec now creates
`build/test_tmp` with `dir_create_all` before writing.

## Tests
- deflate_compress_spec 7/7 (twice, dir pre-existing); `unzip -t` clean.
- deflate_spec, compress_facade_harness, compress_framework,
  compress_shared_helpers, compress_utilities all green on the seed.
