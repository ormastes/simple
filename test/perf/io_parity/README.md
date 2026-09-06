# C/Rust/Simple I/O parity benchmark

## Canonical scope

`run_io_parity_benchmarks.shs` is the canonical broad hosted I/O comparison.
It compares equivalent native C, Rust, and pure-Simple programs for:

- `mmap_direct`: open, shared read-only map, close the descriptor, touch every
  byte, checksum it, and unmap on every iteration;
- `append_at`: start from an equally pre-sized target, open, write all 4096
  bytes at an explicit offset, and close on every iteration;
- invalid-iteration and unknown-case failures: every engine emits one canonical
  marker and exits 2.

The receipt interleaves engines, retains seven cold and seven warm samples per
case, reports p50/p95 latency, p50 MiB/s, and max RSS, and admits only matching
bytes and checksums. `read_text` remains excluded because the runtime cache
semantics are not equivalent.

## Related harness inventory

| Surface | Evidence | Why it is not the canonical broad benchmark |
|---|---|---|
| Startup mmap | `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` | Simple-only startup/preload behavior; no C parity row or retained RSS matrix. |
| Native mmap link | `test/02_integration/compiler/native_mmap_read_link_spec.spl` | Symbol-resolution correctness only; no throughput or cache classes. |
| Cosmos MMIO policy | `test/02_integration/os/cosmos/run_cosmos_hal_mmio_test.shs` and adjacent C/Simple parity fixtures | Host-testable MMIO/policy correctness; requires admitted Stage 4 and does not model bulk file bytes. |
| UART/MMIO implementations | `src/os/realtime/io/uart.spl`, `src/os/kernel/boot/uart16550_mmio.spl`, and platform UART backends | Hardware-facing policy/lifecycle; there is no safe equivalent hosted C/Simple cold/warm byte workload. |
| General cross-language profile | `scripts/check/check-cross-language-perf.shs` | Broad startup/concurrency profile rather than equivalent I/O operations and errors. |

## 2026-08-20 available-artifact baseline

The admitted Simple run is unavailable: `bin/simple` resolves to a Rust
bootstrap seed and has no adjacent Stage 4 provenance. The runner rejected it
before compilation, so these reference-only rows are diagnostic and cannot be
used as a parity PASS or Simple speed claim.

Host: Linux 6.8.0-137-generic x86_64, AMD Ryzen Threadripper 1950X; GCC 13.3.0;
Rust 1.91.1. Workload constants match the receipt schema: 16 MiB mmap fixture,
64 iterations, 4096-byte positioned writes, and seven samples per cache class.

| Case | Cache | Engine | p50 us | p95 us | p50 MiB/s | max RSS KiB | Bytes | Checksum |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| mmap_direct | cold | C | 376203 | 403084 | 2721.935 | 17640 | 1073741824 | 88362650880 |
| mmap_direct | cold | Rust | 326689 | 332648 | 3134.480 | 18252 | 1073741824 | 88362650880 |
| mmap_direct | warm | C | 360268 | 384870 | 2842.328 | 17640 | 1073741824 | 88362650880 |
| mmap_direct | warm | Rust | 299972 | 334498 | 3413.652 | 18252 | 1073741824 | 88362650880 |
| append_at | cold | C | 1101 | 1204 | 227.066 | 1792 | 262144 | 21592384 |
| append_at | cold | Rust | 681 | 1145 | 367.107 | 2048 | 262144 | 21592384 |
| append_at | warm | C | 991 | 1023 | 252.270 | 1792 | 262144 | 21592384 |
| append_at | warm | Rust | 577 | 954 | 433.276 | 2048 | 262144 | 21592384 |

The isolated raw-row SHA-256 was
`9f339b8498ae8a2ac15d263d2cd91bd36dc21b097aba71b93770b7f89ab28365`.

## Pure-Simple optimization evidence

The old mmap checksum crossed the raw pointer boundary once per byte. The new
Simple helper consumes an unaligned prefix and tail byte-wise but reads the
aligned middle eight bytes at a time through the canonical no-GC sync pointer
facade. For the production aligned fixture this changes the deterministic call
count from 1,073,741,824 to 134,217,728 across 64 iterations: exactly 8x fewer
boundary calls. This is structural evidence only. Runtime improvement remains
unmeasured until an admitted Stage 4 compiler can run the full receipt.

`mapped_checksum_selftest.spl` is compiled as a separate native Simple entry,
runs before timing, covers invalid inputs plus lengths 0 through 17 at every
alignment offset 0 through 7, and is independently rebuilt and rerun by receipt
admission. `test/05_perf/io_parity/mapped_checksum_spec.spl` supplies the same
behavior and call-count coverage as a focused SPipe specification.
