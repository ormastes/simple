# Lexer identifier allocation amplification

The optimized lexer allocates 110,361,832 cumulative bytes and 491,538 objects
while tokenizing 1,572,864 source bytes into 163,841 tokens. Live token output
is 56,000,512 bytes and peak live memory above the source fixture is 81,500,592
bytes. See the matched metrics receipt under `doc/10_metrics/text_i18n/`.

Replace eagerly owned token lexemes/identifier strings with source-backed byte
spans and allocate only for escape decoding, normalization, or interning at the
owning boundary. Acceptance requires matched AST/token semantics, allocation
and byte counters, p50/p95/p99, peak/steady RSS, and zero post-drop retention.

