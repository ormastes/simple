# i18n extractor coverage and memory — 2026-08-26

## Scope and correctness

- Owner: `src/compiler_rust/compiler/src/i18n/extractor.rs`
- Isolated crate: `test/01_unit/compiler/i18n/extractor_isolated/`
- Host: x86-64 Linux; nightly LLVM branch coverage and optimized native Rust

The full compiler library is currently unavailable because unrelated import
tracing/counter/lowerer edits produce 21 compile errors. The isolated crate
compiles the real extractor source against the real parser crate. Four tests
pass and cover 28/28 LLVM branches and 20/20 functions (100%). Lines are
285/376 (75.80%); branch closure is the requested owner gate, while unvisited
match arms remain visible for future semantic traversal expansion.

## Joint latency and memory evidence

The fixture is parsed before counters reset. Extraction covers 4,096 explicit
multilingual messages from 303,118 source bytes. Seven fresh-process optimized
runs report:

| Metric | Result |
|---|---:|
| Total latency p50 | 4,332,198 ns |
| Total latency p95 (nearest-rank) | 4,764,404 ns |
| Per-message p50/p95 | 1,057.67 / 1,163.18 ns |
| Allocations | 20,495 (~5.00/message) |
| Cumulative allocated bytes | 2,879,182 |
| Live extraction result bytes | 1,626,128 |
| Peak above parsed fixture | 2,206,445 bytes |
| Retained after result drop | 0 bytes |
| VmHWM | 14,156–14,324 KiB |

This is a rejection baseline for the proposed architecture. Cloned names,
defaults, paths, scopes, and hash-map entries create high allocation density.
The authoritative extractor must emit stable explicit IDs and borrowed/interned
source data, while heuristic plain-string discovery remains a separate audit.

## Reproduction

```text
cargo +nightly llvm-cov --manifest-path \
  test/01_unit/compiler/i18n/extractor_isolated/Cargo.toml \
  --branch --lib --summary-only
cargo run --release --manifest-path \
  test/01_unit/compiler/i18n/extractor_isolated/Cargo.toml \
  --bin extractor-memory-perf
```
