# UTF-16 to UTF-8 conversion retains a high-cost intermediate array

## Status

Open; owner: text/encoding workstream W3.

## Evidence

On 2026-08-26, the retained portable-host performance spec measured
`utf16_to_utf8` over 32,765 UTF-16 code units for 21 samples:

- p50: 926,738 microseconds;
- p95: 1,007,846 microseconds;
- peak process RSS after the workload: 59,336 KiB;
- deterministic aggregate output-length checksum: 1,376,130.

The same run measured UTF-8 validation plus code-point counting over roughly
64 KiB at 1,374 microseconds ASCII p95 and 1,449 microseconds multilingual p95.
The environments and operations differ, so this is not a direct speed ratio;
it is sufficient evidence that conversion needs focused profiling.

Source inspection at `src/lib/common/encoding/utf16.spl` shows
`utf16_to_utf8` calling `utf16_decode_all` to allocate a code-point array and
then allocating/appending the UTF-8 result. This contradicts REQ-004 and NFR-005.

## Required resolution

Implement the stateful `TextDecoder`/`TextSink` path that validates UTF-16 and
writes UTF-8 directly, preserving chunk state and typed progress/errors. Retain
the current implementation as a scalar differential oracle until all chunk and
capacity partitions pass.

## Unblock condition

Close only after the direct streaming implementation has 100% owner branch
coverage, whole-buffer/streaming differential parity for every short partition,
zero O(scalar-count) intermediate allocation in production, and matched-machine
before/after latency plus allocated/copied-byte and peak-RSS receipts.

## Rejected partial optimization

A single-pass loop using `utf16_decode_one` followed by `utf8_encode_one` was
implemented and passed 35/35 UTF-16 unit examples, including explicit malformed
input parity against the old algorithm. It was rejected and reverted because it
still allocated the encoded byte array for every scalar and failed the retained
performance gate:

- before: p50 896,299 us, p95 939,137 us, peak RSS 62,708 KiB;
- candidate: p50 897,159 us, p95 983,181 us, peak RSS 74,804 KiB.

The candidate regressed p95 by about 4.7% and the process RSS observation by
about 19%. The next implementation must write encoded bytes directly into a
reserved sink rather than merely removing one of multiple allocation layers.
