# Raw DEFLATE inflate was module-private; zip/PNG importers failed to resolve

- Date: 2026-11-27
- Status: verification-pending
- Area: stdlib (`src/lib/nogc_sync_mut/compression/gzip/inflate.spl`,
  `src/lib/common/image/deflate_inflate.spl`, `src/lib/common/archive/zip.spl`,
  `src/lib/common/hash/adler32.spl`)
- Reported by: hello-sanity buildrunner twin lane (cannot read deflated zip members)

## Symptom

The pure-Simple RFC 1951 inflater (`_inflate_core`; stored, fixed and dynamic
Huffman) exposed `inflate`, `inflate_bounded`, `inflate_member`, `InflateOut`
and `deflate_block_parse` as plain `fn`/`struct` (module-private). Its importers
(`deflate_inflate.spl`, `compress.spl`, `decompress.spl`, `common/compress/deflate.spl`,
the `nogc_async_mut`/`gc_async_mut` re-exports) worked only because the pairs were
frozen in `scripts/check/private_import_baseline.txt`. The same file also imported
the private `adler32`, and the twin's entry point `zip_extract` (plus the rest of
the zip API) was private too.

The seed module loader (`interpreter_module/module_loader.rs`, private-import
check) only *warns* for a baselined pair, and only when the importing module sits
inside a repo whose root carries that baseline. Anywhere else (sparse/exported
tree, scratch copy, a twin running outside the checkout) the import is a hard
`private fn ... is not visible` error, so the chain `zip_extract -> deflate_inflate
-> inflate` fails to resolve.

## Repro

```
use std.common.image.deflate_inflate.{deflate_inflate}
val d: [u8] = [1u8, 3u8, 0u8, 252u8, 255u8, 65u8, 66u8, 67u8]
print(deflate_inflate(d, 0).len())
```

In-repo: `[visibility-warning] 'inflate_bounded' is a private fn ...` and
`'adler32' is a private fn ...`. In a tree without the baseline (a `git
--work-tree` export of `origin/release/1.0.0`), `deflate_compress_spec.spl`
went 0/7 and `gzip_rfc1951_1952_spec.spl` 77/116; with this fix 6/7 and 82/116
(the remaining failures predate this change and are not in this chain).

## Fix

- `inflate.spl`: new typed `pub fn inflate_raw(data: [u8]) -> Result<[u8], text>`;
  `inflate`, `inflate_bounded`, `inflate_member`, `InflateOut`,
  `deflate_block_parse` made `pub`; `inflate_raw` added to both async re-exports.
- `adler32.spl`: `adler32`, `fletcher32` made `pub`.
- `zip.spl`: zip API (`ZipEntry`, `ZipFile`, `zip_entries`, `zip_extract`,
  `zip_extract_text`, `zip_write_stored`, `zip_write`, `zip_text_file`) made `pub`;
  method-8 members now go through `inflate_raw` and a corrupt member returns
  `None` instead of `Some([])`.
- `deflate_inflate.spl` uses `inflate_raw`.
- The now-public pairs were removed from `private_import_baseline.txt` (ratchet down).

Still baselined in the same neighbourhood (not changed here): `crc32` (imported
by `zip.spl`), `lz77_compress` and `deflate_block_fixed_sync_flush` (imported by
`common/compress/deflate.spl`).

## Prevention

`test/01_unit/lib/nogc_sync_mut/compression/gzip_inflate_raw_spec.spl`: byte-exact
zlib-produced raw streams for a stored, a fixed-Huffman and a dynamic-Huffman
block. Each fixture asserts its own BTYPE, so a "dynamic" fixture cannot quietly be
fixed-Huffman. It also covers the Err path (truncated stream, reserved BTYPE 3),
agreement with the legacy optional API, and a zip `zip_write` -> `zip_extract`
round trip. Seed interpreter: 7/7 pass.

## Throughput (perf finding, open)

1 MiB of word-salad text, zlib level 6 raw (118,350 bytes, dynamic blocks),
`inflate_raw` timed on the seed interpreter
(`C:/dev/wt/bound3x-target/release/simple.exe run`, Windows host): **30.49 s, which is about
0.034 MB/s**. That is a meaningful perf problem for zip/PNG readers on the
interpreter path and is recorded here as open. Native/self-hosted throughput has
not been measured yet.
