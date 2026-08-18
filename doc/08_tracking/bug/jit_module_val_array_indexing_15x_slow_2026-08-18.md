# Arrays sourced from a module-level `val` index 15x slower in the JIT — hoisting does not help

**Status:** OPEN (SIMPLE-CAPABILITY / PERF-REGRESSION root cause)
**Filed:** 2026-08-18
**Found by:** root-causing crc32_text_codegen_lane_14x_slower_than_c_2026-08-18.

## Measured (strict-JIT lane, fixed seed, 1M indexed reads of a 4-elem [i64])

```
val table = MODULE_TABLE (hoisted before loop) : 70,975 us  (~71 ns/read)
identical table built locally via push()       :  4,632 us  (~4.6 ns/read)
```

The hoisted local alias keeps the slow representation: indexing an array
whose identity originates from a module `val` takes a boxed/dispatch path on
every read. Additional finding from the same probes: `text.bytes()` costs
~28 ns/byte in the JIT (58 us for 2,090 bytes) — a second slow builtin path.

## Impact

Any hot loop reading a module-val lookup table (CRC/AES/S-box/base64 tables —
the standard shape for pure-Simple codecs) is deoptimized ~15x regardless of
call-site hygiene. This accounts for the bulk of crc32_text's 14.4x-vs-C gap
(1.045M table reads x ~66 ns delta ≈ 69 ms of the 83 ms).

## Fix

Compiler: give module-val arrays the same unboxed representation/access path
as locals (or const-promote immutable module vals). Library mitigation applied
meanwhile in gzip/crc.spl: per-call local copy of the table (256 pushes ≈ us,
recovers ~4.6 ns/read indexing in the JIT; negligible vs the per-byte loop in
the interpreter).

## Follow-up probes (same day): complete crc32 cost model in the JIT lane

- Indexing a `bytes()`-RETURNED array is fast (~4.1 ns/read) — the slow
  representation is specific to module-val-sourced arrays.
- `text.byte_at(i)` costs ~44 ns/call — worse than bulk bytes()+index; not a
  workaround.
- Post-mitigation per-call budget (2,090-byte body, measured 88 us total vs
  C 11.5 us): bytes() ≈ 58 us (66%, the builtin bulk-conversion bug),
  per-call table copy ≈ 26 us (mitigation cost, removable only by fixing the
  module-val representation), CRC loop itself ≈ 19 us (~9 ns/byte — near-C).
  ⇒ With both compiler fixes the pure-Simple loop is already at parity
  shape; no further library-level work is productive.

## bytes() bulk-fill FIX landed (same day): 26,393 -> 1,964 us per 500x2090B

`rt_string_bytes` (runtime/src/value/collections.rs) now bulk-fills the
exact-capacity array's element slots directly and publishes len once,
instead of one rt_array_push per byte. Measured with a verified fresh build
(first attempt was a cwd-broken cargo run masked by a pipe — the classic
exit-code trap; re-measured after a real rebuild):
- bytes(): ~28 ns/byte -> ~1.9 ns/byte (13x)
- crc32_text codegen lane: 44,128 -> 20,150 us => 3.5x vs C (from 14.4x).
Remaining gap: per-call table copy (~13 ms/500 calls, removable only by the
module-val representation fix) + near-C CRC loop.
