# i18n locale generation coverage and memory — 2026-08-26

## Scope and correctness

- Owner: `src/compiler_rust/compiler/src/i18n/locale.rs`
- Branch harness: `test/01_unit/compiler/i18n/registry_isolated_branch.rs`
- Perf harness: `test/05_perf/text_i18n/i18n_locale_generation_memory_perf.rs`

Nightly LLVM source coverage reports 26/26 branches, 19/19 functions, and
243/243 lines executed. The suite covers default/translated output, stable key
ordering, all supported escapes, malformed declarations, locale filename
fallbacks, file load/write success and errors, generator success and errors,
Unicode round trips, and ignored non-declarations.

## Joint latency and memory evidence

An optimized native workload generates 4,096 multilingual declarations and
352,350 output bytes. Seven fresh-process samples report:

| Metric | Result |
|---|---:|
| Total generation p50 | 2,057,469 ns |
| Total generation p95 (nearest-rank) | 2,108,366 ns |
| Per-message p50/p95 | 502.31/514.74 ns |
| Allocations | 20,495 (about 5.00/message) |
| Live generated output capacity | 385,024 bytes |
| Transient peak above fixture | 577,767 bytes |
| Retained after output drop | 0 bytes |
| Process VmHWM | 3,072 KiB |

The owner is branch-complete, but the allocation count is a rejection baseline:
`format!` creates per-entry temporaries before appending to the output `String`.
The builder/sink redesign must preflight/reserve and append escaped runs without
per-message temporary strings.

