# Bootstrap lint JSON validation accepted malformed output — 2026-07-23

**Status:** SOURCE FIXED / FRESH STAGE 4 QUALIFICATION PENDING

## Reproduction

The essential-tools smoke accepted a lint line that began with an allowed
`{"type":"lint-..."` prefix even when the JSON record was truncated or had
invalid trailing syntax.

## Root cause and fix

The gate used a prefix-only `awk` check instead of parsing each JSONL record.
It now runs a bounded pure-Simple validator backed by the shared strict JSON
parser. The parser rejects invalid escapes, raw control characters, malformed
numbers, and trailing tokens; JSONL rejects empty/interior-blank, truncated,
and unreadable input. Focused parser/JSONL and bootstrap-wiring contracts cover
the regression. The temporary bootstrap interpreter also returned exit 1 for
an unreadable validator input. The current self-hosted `check src/lib` still
crashes with exit 139, so the aggregate requires a fresh Stage 4 binary run.
