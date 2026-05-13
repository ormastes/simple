# CRC32 native global table cache segfault

Date: 2026-05-13
Status: Open

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

- `src/compiler_rust/target/release/simple check src/os/crypto/crc32.spl test/unit/os/crypto/crc32_kat_spec.spl test/perf/port_algorithms/port_algorithms_simple.spl`
- `src/compiler_rust/target/release/simple test test/unit/os/crypto/crc32_kat_spec.spl --mode=interpreter --no-cache`

Native benchmark failure:

```bash
SIMPLE_BIN=src/compiler_rust/target/release/simple \
SIMPLE_RUNTIME_PATH=src/compiler_rust/target/release \
SIMPLE_NATIVE_ALL_PATH=src/compiler_rust/target/release \
SIMPLE_LLVM_PROBE=0 SIMPLE_DISASM_PROBE=0 SIMPLE_BENCH_SAMPLES=3 \
test/perf/port_algorithms/run_port_algorithm_benchmarks.shs
```

The run printed the Simple XXHash64 row, then crashed before the CRC32 row:

```text
Segmentation fault (core dumped)
```

## Impact

CRC32 still rebuilds its 1 KiB table per one-shot/update call. This keeps the
performance row below the faster-than-C/Rust target in the port algorithm gate.

## Next Step

Fix native codegen/runtime handling for mutable module-level array caches, or add
a verified static-table representation for byte lookup tables. Do not re-enable
the CRC table cache until the native benchmark runs without crashing.
