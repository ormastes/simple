# Brotli large-boundary decode timeout

Date: 2026-05-13
Status: Fixed (2026-05-19)
Severity: Compression verification blocker

## Evidence

During async/GC compression facade parity verification, the existing canonical
Brotli edge spec exceeded the Simple test runner watchdog.

Command:

```bash
bin/simple test test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl --mode=interpreter --clean
```

Observed result: the `round-trips a 65536-byte payload in a single maximum
uncompressed meta block` example timed out after 60s.

The smaller canonical Brotli LZ77 round-trip suite passed:

```bash
bin/simple test test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_lz77_round_trip_spec.spl --mode=interpreter --clean
```

## Impact

The new `std.nogc_async_mut.compression.*` and
`std.gc_async_mut.compression.*` facades pass smoke coverage, but large Brotli
boundary behavior remains weakly verified until this performance issue is fixed
or the test is split into a bounded tier.

## Fix (2026-05-19)

Replaced byte-at-a-time push loops with `rt_bytes_alloc` preallocated buffers
and index-assignment in all four hot paths:

- `bit_reader.spl` — `brotli_bits_read_bytes`: preallocate `n` bytes, assign
  by index instead of `out.push(r.data[i])` per iteration.
- `bit_writer.spl` — `brotli_bits_write_bytes`: preallocate `existing + payload`
  bytes, copy both segments by index instead of appending one byte at a time.
- `encoder.spl` — `_slice`: preallocate `len` bytes, assign by index instead of
  `out.push(data[offset + i])`.
- `decoder.spl` — uncompressed meta-block merge: preallocate `old_len + mlen`
  output, copy both segments by index instead of `new_output.push(raw.bytes[i])`.

Each of the above loops runs 65536 times for a 64 KiB payload. Preallocating
once and writing by index eliminates the interpreter-level per-push overhead
that caused the watchdog timeout.
