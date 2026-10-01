# Lexer identifier coverage and memory — 2026-08-26

## Branch closure

Owner: `src/compiler_rust/parser/src/lexer/identifiers.rs`.

The initial 302-library-test LLVM baseline executed 168/304 branches (55.26%),
5/6 functions, and 363/610 lines. A systematic external test matrix was added
for all keyword/contextual spellings, suspension forms, prefixed strings,
i18n forms, pointcuts, atoms, symbols, every custom-block kind, every
short-circuit prefix, nested braces, strings, escapes, and comment states.

The final bounded cycle passes 307/307 library tests and executes 302/302
branches (100%), 6/6 functions, and 612/613 lines. An impossible optional-pop
branch was replaced with an explicit brace-depth invariant assertion rather
than excluded from the denominator.

The complete parser integration attempt is not release-green: an unrelated
`control_flow` test currently expects no `TsArrowFunction` diagnostic but
receives one. Therefore this receipt closes the identifier owner’s library
denominator only; it does not claim full parser-suite readiness.

## Joint native latency and memory

Workload: 32,768 lines, 1,572,864 UTF-8 bytes, 163,841 tokens, ASCII-leading
identifiers with Korean continuations. Seven optimized fresh processes:

| Metric | Result |
|---|---:|
| Latency p50 | 133,383,885 ns |
| Latency p95 (nearest-rank) | 148,326,920 ns |
| Throughput at p50 | 11.25 MiB/s |
| Allocations | 491,538 (~3.00/token) |
| Cumulative allocated bytes | 110,361,832 |
| Live token output | 56,000,512 bytes |
| Peak live bytes above fixture | 81,500,592 |
| Retained after token drop | 0 bytes |
| Process VmHWM | 61,868–61,880 KiB |

This is a rejection baseline. Cumulative allocation is about 70.16 bytes per
input byte and live output about 342 bytes/token. The planned borrowed-token
model must report lexemes as source spans except when decoding is required.
Because this measures the Rust parser rather than the required pure-Simple
frontend, it is diagnostic evidence and must not populate either mandatory
`parser_ascii` or `parser_multilingual` performance row.
