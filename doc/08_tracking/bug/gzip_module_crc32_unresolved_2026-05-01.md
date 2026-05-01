# Bug: gzip module fails to load — `crc32_calculate` unresolved

- **Date:** 2026-05-01
- **Status:** Open
- **Module:** `src/lib/nogc_sync_mut/compression/gzip/`
- **Discovered by:** HTTPS/HTTP2 compression+cipher pass, Phase 1B integration probe

## Symptom

Calling `gzip_compress(payload: [u8], level: i64)` from
`src/lib/nogc_sync_mut/compression/gzip/compress.spl` from any external
caller fails at runtime with:

```
error: semantic: function `crc32_calculate` not found
```

Reproduction (`/tmp/gzip_probe.spl`, ran via `bin/simple`):

```simple
use std.nogc_sync_mut.compression.gzip.compress.{gzip_compress}

fn main() -> i64:
    val payload: [u8] = [0x61u8, 0x62u8, 0x63u8]
    val compressed = gzip_compress(payload, 6)
    ...
```

The error fires before any real work — `gzip_compress` calls
`crc32_calculate(data)` on its first line and the symbol does not resolve.

## Suspected root cause

The gzip module declares its dependencies via `mod` at the top of
`compress.spl`:

```
mod compression.gzip.types
mod compression.gzip.crc
mod compression.gzip.header
...
```

The `crc.spl` module presumably defines `crc32_calculate`, but its export
is not visible to `compress.spl` callers when the module is imported
externally. Possibilities:

1. `crc32_calculate` is private to `crc.spl` and `compress.spl` only works
   when the whole gzip module is loaded as a single internal unit — i.e.
   it has no validated external API.
2. The `mod compression.gzip.crc` form imports the module but does not
   bring its functions into scope; `compress.spl` would need an explicit
   `use compression.gzip.crc.{crc32_calculate}` (or equivalent) which is
   missing.
3. The function is named differently in `crc.spl` than what `compress.spl`
   calls.

The fact that this code appears never to have been called from outside
the gzip module (no `use std.nogc_sync_mut.compression.gzip` references
exist anywhere in `src/`, `examples/`, or `test/`) strongly suggests
option 1 or 2.

## Impact

- HTTP server cannot offer `Content-Encoding: gzip` until this is fixed.
- Phase 1B compression dispatcher
  (`src/lib/nogc_async_mut/http_server/compression.spl`) has the gzip
  arm intentionally returning `Err` to surface this gap rather than
  silently falling back to identity.
- Browsers without zstd support (anything pre-Chrome 123 / pre-Firefox
  126) will not see compressed responses from Simple's HTTP server until
  gzip lands.

## Suggested fix

1. Read `src/lib/nogc_sync_mut/compression/gzip/crc.spl` and confirm
   that `crc32_calculate` is exported (i.e. is a top-level `fn`, not
   inside a class or under an `_` prefix).
2. Add the explicit `use` statement at the top of `compress.spl`,
   `header.spl`, etc. — wherever cross-module symbols are referenced.
3. Add an `__init__.spl` re-export so external callers can write
   `use std.nogc_sync_mut.compression.gzip.{gzip_compress, gzip_decompress}`
   directly.
4. Type the public entry points: `fn gzip_compress(data: [u8], level: i64) -> [u8]?`
   replacing the current untyped declaration.
5. Add a `gzip_module_smoke_spec.spl` covering empty input, small input,
   and a 1 KiB round-trip.
6. Once typed and tested, register `CompressionCodec.gzip` in
   `src/lib/common/compress/types.spl` and add the gzip arm to
   `compress/mod.spl::try_compress_bytes` and `decompress_bytes` so the
   common compress façade exposes it. (This requires either moving the
   gzip module under `lib/common/compress/gzip/` since `lib/common`
   cannot depend on `lib/nogc_sync_mut`, or building a thin façade
   shim in a third tier.)
7. After the façade lands, simplify the http_server compression
   dispatcher's gzip arm from `Err(...)` to a real call.

## Workaround

None at the application layer. The dispatcher's explicit `Err` is the
only safe behaviour today — silently falling back to identity would
mislead clients that explicitly requested gzip with `Accept-Encoding: gzip`.

## Cross-references

- Plan: `/home/ormastes/.claude/plans/see-next-and-impl-ethereal-scott.md` Phase 1
- Dispatcher: `src/lib/nogc_async_mut/http_server/compression.spl`
- Compress façade: `src/lib/common/compress/{mod,types}.spl`
