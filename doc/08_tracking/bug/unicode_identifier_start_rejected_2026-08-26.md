# Non-ASCII identifier starts are rejected by the lexer
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

`scan_identifier` accepts Unicode alphanumeric continuation characters, but
the lexer dispatcher calls it only for ASCII `[A-Za-z_]`. A source identifier
beginning with Korean, Greek, Cyrillic, Arabic, CJK, or another non-ASCII XID
start is emitted as `Unexpected character` before identifier scanning.

Do not patch this with `char::is_alphabetic()` as the permanent rule. Implement
the architecture’s pinned Unicode 17 UAX #31 `XID_Start`/`XID_Continue` tables,
ASCII fast path, NFC symbol identity, original-spelling spans, and UTS #39
diagnostics together. Add conformance, normalization-equivalence, confusable,
mixed-script, invalid UTF-8 ingress, and performance/memory tests.


