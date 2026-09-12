# Non-ASCII identifier starts are rejected by the lexer

**Status:** OPEN (unverified 2026-09-12)

`scan_identifier` accepts Unicode alphanumeric continuation characters, but
the lexer dispatcher calls it only for ASCII `[A-Za-z_]`. A source identifier
beginning with Korean, Greek, Cyrillic, Arabic, CJK, or another non-ASCII XID
start is emitted as `Unexpected character` before identifier scanning.

Do not patch this with `char::is_alphabetic()` as the permanent rule. Implement
the architecture’s pinned Unicode 17 UAX #31 `XID_Start`/`XID_Continue` tables,
ASCII fast path, NFC symbol identity, original-spelling spans, and UTS #39
diagnostics together. Add conformance, normalization-equivalence, confusable,
mixed-script, invalid UTF-8 ingress, and performance/memory tests.


## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
