# Rust i18n registry coverage and memory — 2026-08-26

## Scope

- Owner: `src/compiler_rust/compiler/src/i18n/registry.rs`
- Authoritative isolated harness: `test/01_unit/compiler/i18n/registry_isolated_branch.rs`
- Joint latency/memory harness: `test/05_perf/text_i18n/i18n_registry_memory_perf.rs`
- Host: x86-64 Linux; optimized `rustc --edition=2021 -O`

The isolated harness includes the real registry and locale parser sources. It
was necessary because unrelated in-progress compiler edits leave the full Rust
crate uncompilable (`read_trace`, import counters, and `Lowerer` fields do not
currently agree).

## Correctness and branch evidence

Twelve isolated tests pass. Nightly LLVM source coverage for the registry owner
is 181/181 lines, 29/29 functions, and 10/10 branches (100%). Covered behavior
includes current/default lookup, missing keys/maps, file success/error,
merge/override, clear/reset, loaded-locale queries, placeholders, and
thread-local isolation.

## Joint latency and memory evidence

Workload: 4,096 multilingual messages and 100,000 successful lookups. Seven
fresh-process samples produced:

| Metric | Result |
|---|---:|
| Lookup latency p50 | 194.50 ns/op |
| Lookup latency p95 (nearest-rank) | 330.10 ns/op |
| Catalog live heap | 958,791 bytes |
| Lookup allocations | 2.000/op |
| Peak tracked live heap | 1,360,684 bytes |
| Process VmHWM | 3,072–3,328 KiB |
| Retained after `clear()` | 308 bytes |

The two allocations are architectural: `lookup()` clones the current locale
and clones the returned message. `clear()` removes entries but retains outer
`HashMap` capacity. This is valid prototype evidence, not acceptance evidence
for the proposed compiled/borrowed catalog, whose required hot lookup gate is
zero allocations.

## Reproduction

```text
rustc +nightly --edition=2021 -C instrument-coverage \
  -Z coverage-options=branch --test \
  test/01_unit/compiler/i18n/registry_isolated_branch.rs

rustc --edition=2021 -O \
  test/05_perf/text_i18n/i18n_registry_memory_perf.rs
```

