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
