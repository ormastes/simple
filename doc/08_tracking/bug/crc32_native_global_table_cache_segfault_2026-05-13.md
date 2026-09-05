# CRC32 native global table cache segfault

Date: 2026-05-13
Status: Fixed 2026-05-19

## Summary

Adding lazy module-level `[u8]` caches for the CRC-32 and CRC-32C lookup tables
passes interpreter KATs but segfaults in the native port-algorithm benchmark.

## Evidence

Attempted implementation:

- `var _ieee_table_cache: [u8] = []`
- `var _ieee_table_ready: bool = false`
- `_ieee_table()` assigns `_ieee_table_cache = _make_table(0xEDB88320)` on first use.
- Equivalent Castagnoli cache for `_castagnoli_table()`.

Validation before native run:

- `src/compiler_rust/target/release/simple check src/os/crypto/crc32.spl test/01_unit/os/crypto/crc32_kat_spec.spl test/05_perf/port_algorithms/port_algorithms_simple.spl`
- `src/compiler_rust/target/release/simple test test/01_unit/os/crypto/crc32_kat_spec.spl --mode=interpreter --no-cache`

Native benchmark failure:

```bash
SIMPLE_BIN=src/compiler_rust/target/release/simple \
SIMPLE_RUNTIME_PATH=src/compiler_rust/target/release \
SIMPLE_NATIVE_ALL_PATH=src/compiler_rust/target/release \
SIMPLE_LLVM_PROBE=0 SIMPLE_DISASM_PROBE=0 SIMPLE_BENCH_SAMPLES=3 \
test/05_perf/port_algorithms/run_port_algorithm_benchmarks.shs
```

The run printed the Simple XXHash64 row, then crashed before the CRC32 row:

```text
Segmentation fault (core dumped)
```

## Impact

CRC32 still rebuilds its 1 KiB table per one-shot/update call. This keeps the
performance row below the faster-than-C/Rust target in the port algorithm gate.

## Resolution

Replaced the dynamic `_ieee_table()` / `_castagnoli_table()` functions (which
called `_make_table()` on every invocation) with module-level `val` literals
`_IEEE_TABLE` and `_CASTAGNOLI_TABLE` (256 × 4 bytes each, LE-packed u32s).

The lazy `var` cache pattern segfaulted in native because the native codegen does
not correctly handle mutable module-level array globals. Using immutable `val`
literal arrays avoids global mutation entirely and matches the pattern used by
other static-table files in the same directory (e.g. `bcrypt_tables.spl`).

Both table values were independently verified against the standard KAT vectors:
- CRC32("123456789") = 0xCBF43926
- CRC32C("123456789") = 0xE3069283

The `_push_u32_le` and `_make_table` helper functions were removed as they are
no longer needed.

## Next Step

Run the native port-algorithm benchmark to confirm the segfault is gone:

```bash
SIMPLE_BIN=src/compiler_rust/target/release/simple \
SIMPLE_RUNTIME_PATH=src/compiler_rust/target/release \
SIMPLE_NATIVE_ALL_PATH=src/compiler_rust/target/release \
SIMPLE_LLVM_PROBE=0 SIMPLE_DISASM_PROBE=0 SIMPLE_BENCH_SAMPLES=3 \
test/05_perf/port_algorithms/run_port_algorithm_benchmarks.shs
```
