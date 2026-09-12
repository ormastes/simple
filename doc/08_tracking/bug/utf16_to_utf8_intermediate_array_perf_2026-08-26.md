# UTF-16 to UTF-8 conversion retains a high-cost intermediate array

**Status:** OPEN (unverified 2026-09-12)

## Status

Open; owner: text/encoding workstream W3. The intermediate-allocation half is
FIXED (2026-09-12, see "2026-09-12 remediation"); the streaming
`TextDecoder`/`TextSink` requirement below is a feature and remains open.

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


## 2026-09-12 remediation (intermediate allocations removed; 4.4x)

`utf16_to_utf8` is now a single fused pass in
`src/lib/common/encoding/utf16.spl:166-212`. It decodes inline instead of
calling `utf16_decode_all`, and appends UTF-8 bytes straight into the result
instead of calling `utf8_encode_one`. That removes both O(scalar-count)
intermediates: the code-point array, and the 1..4-element array allocated per
code point. `utf16_decode_all` / `utf16_encode_all` / `utf8_encode_one` are
untouched and remain the differential oracle this record asks to retain.

**Two corrections to the evidence above, both measured.**

1. The cost is **linear, not quadratic** — 0.94 s at 32,765 units and ratio ~4.1
   at 4x n on the deployed seed. The record's 926 ms p50 reproduces exactly; it
   is a constant factor, not an asymptote.
2. The intermediate code-point array is the **smaller** half of that constant
   factor. Running all three implementations in one process (32,765 units, min
   of 3, the only way to beat this host's ~2x round-to-round noise):

   | implementation | min us | speedup |
   |---|---|---|
   | `utf16_decode_all` then encode (as filed) | 1,039,755 | 1.00x |
   | fused decode, still calling `utf8_encode_one` | 612,452 | 1.70x |
   | fused decode + inlined UTF-8 encode (shipped) | 301,556 | 3.45x |

   A first attempt that fused only the decode measured *worse* through the spec
   harness (506 ms -> 531 ms). That was host noise, and is why the comparison
   below is relative and in-process rather than an absolute wall budget.

**Fix-test:** `test/05_perf/text_i18n/utf16_to_utf8_direct_conversion_perf_spec.spl`
— a differential-parity example (empty input, BMP, surrogate pair, lone high,
lone low, truncated trailing high, double high, out-of-range units) plus a
same-process speedup-vs-oracle receipt.

**How that receipt is measured, and why it is not a wall budget.** This host is
shared and heavily contended. An absolute budget is hopeless (identical
back-to-back runs of one binary differ by >2x), and `min` over independent
samples is barely better — it picks each path's luckiest run separately, and
across four runs of the FIXED code it produced 1.4x, 2.9x, 7.0x and 7.2x, i.e.
it would flake one time in four against a 2x bound. The spec therefore times
both paths back to back inside one round, takes the PAIRED ratio, and asserts a
MAJORITY of five rounds clears 2x. One scheduler stall then moves one ratio, not
the verdict.

Deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`, 50093192 bytes,
2026-09-06 09:59:11 (per-round speedup x100, `cleared` of 5 rounds):

| | rounds | cleared | result |
|---|---|---|---|
| RED (as filed) | `[174, 48, 91, 196, 102]` | 0/5 | 2 examples, 1 failure |
| RED (as filed, repeat) | `[79, 76, 145, 95, 108]` | 0/5 | 2 examples, 1 failure |
| GREEN (fused) | `[244, 350, 528, 492, 385]` | 5/5 | 2 examples, 0 failures |
| GREEN (repeat) | `[395, 392, 490, 528, 130]` | 4/5 | 2 examples, 0 failures |
| GREEN (repeat) | `[597, 460, 1701, 424, 576]` | 5/5 | 2 examples, 0 failures |

Also green on a binary freshly built from `origin/main` = `7352f99898c`
(`src/compiler_rust/target/release/simple`, 51226288 bytes, 2026-09-12
10:01:32), which measured the fused path faster still (4.4x on a min-of-3 run).
Both are interpreter-lane receipts; the spec runner defaults to the interpreter.

Retained lane, unchanged corpus, after the fix — note the **identical**
deterministic checksum 1,376,130, which is the correctness receipt:

```
text_perf operation=utf16_to_utf8 samples=21 input_units=32765
  p50_us=325092 p95_us=577625 peak_rss_kib=100208 checksum=1376130
```

(as filed: p50 926,738 / p95 1,007,846 / peak RSS 59,336 KiB — RSS is not
comparable across hosts and is not claimed as an improvement here.)

Nearest specs, all green on the fixed tree:
`test/01_unit/lib/common/encoding/utf16_spec.spl` 34/34,
`test/unit/lib/common/encoding/utf16_spec.spl` 32/32,
`test/01_unit/lib/common/encoding/utf8_spec.spl` 58/58,
`test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl` 3/3,
`test/05_perf/text_i18n/utf8_internationalized_text_memory_spec.spl` 3/3.

Mechanism rows `UTF16FUSE*` added to
`scripts/check/check-perf-regression-tests.shs` so a stale-snapshot clobber
cannot silently restore either allocation.

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

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).
