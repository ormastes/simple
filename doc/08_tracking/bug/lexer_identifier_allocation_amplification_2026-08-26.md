# Lexer identifier allocation amplification

**Status:** OPEN (unverified 2026-09-12)

The optimized lexer allocates 110,361,832 cumulative bytes and 491,538 objects
while tokenizing 1,572,864 source bytes into 163,841 tokens. Live token output
is 56,000,512 bytes and peak live memory above the source fixture is 81,500,592
bytes. See the matched metrics receipt under `doc/10_metrics/text_i18n/`.

Replace eagerly owned token lexemes/identifier strings with source-backed byte
spans and allocate only for escape decoding, normalization, or interning at the
owning boundary. Acceptance requires matched AST/token semantics, allocation
and byte counters, p50/p95/p99, peak/steady RSS, and zero post-drop retention.


## Triage 2026-09-12
No cheap repro attempted in this bulk pass (rule D: newer than 45 days, left open). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
