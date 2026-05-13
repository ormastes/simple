# Brotli large-boundary decode timeout

Date: 2026-05-13
Status: Open
Severity: Compression verification blocker

## Evidence

During async/GC compression facade parity verification, the existing canonical
Brotli edge spec exceeded the Simple test runner watchdog.

Command:

```bash
bin/simple test test/unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl --mode=interpreter --clean
```

Observed result: the `round-trips a 65536-byte payload in a single maximum
uncompressed meta block` example timed out after 60s.

The smaller canonical Brotli LZ77 round-trip suite passed:

```bash
bin/simple test test/unit/lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.spl --mode=interpreter --clean
```

## Impact

The new `std.nogc_async_mut.compression.*` and
`std.gc_async_mut.compression.*` facades pass smoke coverage, but large Brotli
boundary behavior remains weakly verified until this performance issue is fixed
or the test is split into a bounded tier.

## Next Steps

- Profile `brotli_encode_uncompressed` and `brotli_decode` on 64 KiB payloads.
- Replace byte-at-a-time append/copy hot paths with chunked or preallocated
  buffers where possible.
- Keep a smaller fast unit test and move the 64 KiB case to an explicit
  slow/perf tier if the interpreter cannot reasonably execute it under the
  default watchdog.
