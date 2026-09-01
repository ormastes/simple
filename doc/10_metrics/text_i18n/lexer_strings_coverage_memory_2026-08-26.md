# String lexer coverage and memory — 2026-08-26

## Bounded coverage status

Owner: `src/compiler_rust/parser/src/lexer/strings.rs`.

The inherited LLVM baseline is 141/198 branches (71.21%), 12/13 functions, and
326/410 lines. New external matrices cover raw single/double/triple strings,
typed suffixes, Unicode suffixes, escapes, newline/EOF failures, f-string
backtracking, nested strings/braces/parens, transpose, format specifications,
and helper decision tables.

The audit found and fixed byte/scalar coordinate mixing in
`scan_string_unit_suffix`: it used UTF-8 byte length as the number of scalar
`advance()` calls. Consumption now uses `suffix.chars().count()`.

The lane hit its three-cycle cap before a new coverage artifact was admissible:
one compile failure exposed private helper visibility, one mistaken filter ran
zero tests, and the full lexer run found a raw-string fixture that reaches label
disambiguation rather than raw scanning. The fixture was corrected to call the
authoritative scanner directly, but is not re-run this session. The owner stays
open at its last measured baseline; no improved coverage claim is made.

## Joint native latency and memory

Workload: 16,384 multilingual formatted strings, 1,294,336 input bytes, 81,921
tokens. Seven optimized fresh processes:

| Metric | Result |
|---|---:|
| Latency p50 | 105,516,237 ns |
| Latency p95 (nearest-rank) | 172,340,233 ns |
| Throughput at p50 | 11.70 MiB/s |
| Allocations | 458,769 (~28.00/string) |
| Cumulative allocated bytes | 62,143,720 (~3,792.95/string) |
| Live token output | 31,735,808 bytes (1,937/string) |
| Peak live bytes above fixture | 43,738,698 (~2,669.60/string) |
| Retained after token drop | 0 bytes |
| Process VmHWM | 37,068–37,408 KiB |

This Rust receipt is diagnostic only and cannot populate mandatory pure-Simple
parser rows. It is a rejection baseline for cloned lexer state, literals,
expressions, format strings, parts, and lexemes.

