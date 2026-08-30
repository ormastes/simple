# Production lexer memory evidence — 2026-08-26

The `CoreLexer` memory lane passes 3/3. Every corpus reaches `TOK_EOF` within a
fixed cap and rejects dead kind 0 behavior.

| Corpus | UTF-8 bytes | Tokens |
|---|---:|---:|
| ASCII | 2,212 | 641 |
| Multilingual strings | 4,342 | 321 |
| Named i18n interpolation | 2,806 | 385 |
| General syntax stress | 351 | 100 |

The final bounded cycle also scanned 28 lexical edge probes (140 tokens), each
reaching real EOF. Production `lexer_struct.spl` coverage is 59% lines
(497/836) and 51% branches (99/194), up from the first cycle's 30%/21%. This is
not 100% closure; the remaining general-language and recovery paths require
the broader compiler lexer campaign.

Lexer construction is inside the snapshot because `make_core_lexer` currently
materializes `source.chars()`, adding O(scalar-count) storage before scanning.
The deployed interpreter exposes no trustworthy allocation, retained-byte, or
process-HWM counters, so zero-valued fields are classified as unavailable.

Latency/throughput was not measured: the host load was 13.24/25.32/27.73 with
multiple unrelated `simple` and `rustc` processes saturating CPUs. A quiet,
matched baseline remains required.
