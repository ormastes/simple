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

## RE-MEASURED 2026-09-06 (aarch64) — this finding is CLOSED at 1.2x

**Host:** aarch64 Linux, 20 CPUs, shared/loaded (a full bootstrap plus three
other agent sessions concurrent). **Binary:** the Rust bootstrap seed at
`bin/release/aarch64-unknown-linux-gnu/simple`, 50,093,192 bytes, sha256
prefix `3d120a6f9ab5704b` — it prints the `bootstrap seed only` banner, so
this is the same binary CLASS as the original x86_64 measurement, not a
self-hosted build. **Method:** identical in shape to the record above —
`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 bin/simple run`, 500 iters,
body_len 2090, output equality (`crc32_text(body) == rt_crc32_text(body)`)
asserted in-run BEFORE any timing, exit 0 with no strict-mode refusal.
Harness: `bench_crc32_codegen.spl` (scratchpad, not committed), a `run`-lane
twin of the committed interpreter-lane spec
`test/05_perf/lib/crc32_text_c_vs_simple_perf_spec.spl`.

```
lane=codegen iters=500 body_len=2090
c_us      = 5695 / 5681 / 5686      (three consecutive runs)
simple_us = 7030 / 6978 / 6996
ratio     = 1.23x / 1.23x / 1.23x
```

**The 14.4x is gone and the record above was stale.** The two fixes it
already describes — the `rt_string_bytes` bulk-fill and the module-val
initializer fix that let `gzip/crc.spl` drop its `_table_copy()` mitigation
(removed 2026-08-20; the file's own comment records this) — both landed and
are in the deployed seed. Nothing further was needed for this kernel: the
per-byte CRC loop is now within noise of a C extern call, and `c_us` here is
extern-call overhead, so 1.23x is effectively parity for this shape.

Re-measured after the 2026-09-06 runtime changes described in the sibling
record (`codegen_lane_still_slow_base64url_utf8_time_utils_2026-08-18.md`):
`simple_us = 6819`, ratio 1.20x — no regression, no material gain, as
expected since `crc32_text` neither joins nor converts bytes to text.

**Status change: OPEN -> RESOLVED for the codegen lane.** The root-cause
candidate list above (bounds checks per byte, boxed i64 arithmetic, no
register promotion) was NOT what the gap turned out to be, and none of those
were fixed — measured directly on this host, a `[u8]` indexed-store loop runs
at ~3 ns/byte and a bare `push` loop at ~2 ns/byte, i.e. the JIT's scalar
array code is already fine. Do not re-open this against those hypotheses.
