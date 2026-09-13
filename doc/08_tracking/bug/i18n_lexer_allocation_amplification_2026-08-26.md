# i18n lexer allocation amplification

**Status:** OPEN (unverified 2026-09-12)

Lexing 16,384 multilingual interpolated messages performs 262,160 allocations
(~16/message), allocates 34,487,528 bytes cumulatively (~2.1 KiB/message), keeps
19,922,944 bytes live in tokens (~1.2 KiB/message), and peaks at 26,476,552
bytes above the source fixture.

Unify ordinary/f/i18n scanning around borrowed source spans. Store interpolation
expressions as byte ranges and allocate decoded owned segments only when escapes
transform the source. Acceptance requires exact token/AST/extraction parity,
joint p50/p95/p99, allocations/bytes, steady/peak RSS, and post-drop retention.


## Triage 2026-09-12
No cheap repro attempted in this bulk pass (rule D: newer than 45 days, left open). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
