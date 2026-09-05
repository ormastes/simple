# crc32_text 14.4x slower than C in the codegen (strict-JIT) lane

**Status:** OPEN (PERF-REGRESSION / SIMPLE-CAPABILITY)
**Filed:** 2026-08-18
**Found by:** first codegen-lane parity measurement for C-MIG-0001
(binary_runtime_hardening goal 3).

## Measurement (fresh seed with the strict-JIT fail-open fix + bare-assign
local minting fix, so silent interpreter fallback is IMPOSSIBLE — a fallback
hard-errors)

```
lane=strict-jit  iters=500  body_len=2090
simple_jit_us = 82,911     (crc32_text, pure Simple, table-driven)
c_interp_us   =  5,767     (rt_crc32_text extern; extern-call overhead only)
ratio ≈ 14.4x  → verdict FAIL (>2% band), massive improvement over the
                 interpreter lane's 542x but not parity.
```

Output equality verified in-run before timing (mismatch aborts).

## Root-cause candidates (perf workflow taxonomy)

- bounds checks on `raw[i]` and `table[index]` per byte (2090 x 500 = 1M+ each)
- tagged/boxed i64 arithmetic in the JIT for `(crc >> 8) ^ table[index]`
- `_CRC32_TABLE` module-val access cost per read (global load vs register)
- no 4/8-byte table slicing (C does 1 byte/iter too, so algorithmic parity —
  the gap is per-op codegen cost, not algorithm)

## Next

Profile MIR -> Cranelift for the loop body; prefer a compiler/runtime fix
(bounds-check elision on proven-in-range induction vars) so every pure-Simple
byte loop benefits, per the migration process rule. Tracked in
c_migration_inventory.sdn C-MIG-0001 perf_status.

## Update (same day): 14.4x -> 7.6x after root-cause fix #1

Root cause isolated to two measured components (probes in
jit_module_val_array_indexing_15x_slow_2026-08-18.md):
1. module-val array indexing ~71 ns/read vs 4.6 ns local (FIXED at library
   level: per-call `_table_copy()` in gzip/crc.spl) -> 82,911 -> 44,128 us.
2. `text.bytes()` ~28 ns/byte (29 ms of the remaining 44 ms) — still OPEN,
   compiler/runtime builtin path.

Both lanes re-verified after the fix: crosslang differential 5/5;
interpreter perf spec 1/1 (copy cost negligible there, as predicted).
