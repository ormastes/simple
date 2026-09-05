# i18n lexer coverage and memory — 2026-08-26

## Bounded branch audit

Owner: `src/compiler_rust/parser/src/lexer/i18n.rs`.

The inherited baseline executed 24/60 branches (40%), 7/7 functions, and
110/178 lines. New external tests cover empty/nonempty literals, interpolation
at the start and after text, nested expressions, escaped braces, Unicode,
character/error/unterminated escapes, newline/EOF termination, single closing
braces, one/two/three quote states, and single/triple forms. They pass 2/2; the
complete library suite passes 309/309.

The second measurement reaches 53/60 branches (88.33%) and 176/178 lines. Six
remaining branches belong to `assert!(matches!(... if ...))` guards inside the
owner’s inline tests; taking them would fail the tests. The seventh production
branch (triple interpolation with an empty leading literal) received a test,
but the third measurement failed because this nightly requires an additional
crate-level unstable feature for `#[coverage(off)]`. The unsupported attribute
was removed. Under the three-cycle cap, the owner remains open; no 100% claim is
made.

## Joint native latency and memory

Workload: 16,384 multilingual interpolated messages, 1,572,864 input bytes,
32,769 tokens. Seven optimized fresh processes:

| Metric | Result |
|---|---:|
| Latency p50 | 41,253,138 ns |
| Latency p95 (nearest-rank) | 45,510,422 ns |
| Throughput at p50 | 36.36 MiB/s |
| Allocations | 262,160 (~16.00/message) |
| Cumulative allocated bytes | 34,487,528 (~2,105/message) |
| Live token output | 19,922,944 bytes (~1,216/message) |
| Peak live bytes above fixture | 26,476,552 (~1,616/message) |
| Retained after token drop | 0 bytes |
| Process VmHWM | 25,828–25,836 KiB |

This Rust measurement is diagnostic and cannot populate the mandatory
pure-Simple parser rows. It is a rejection baseline for cloned literals,
expression strings, owned part vectors, and owned token lexemes.

