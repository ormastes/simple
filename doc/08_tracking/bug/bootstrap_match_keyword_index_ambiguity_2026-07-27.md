# Bootstrap Parser Misreads `match[0]` As A Match Expression

- **Date:** 2026-07-27
- **Area:** pure-Simple parser / keyword identifiers
- **Severity:** high — blocks the strict Stage 4 full-CLI bootstrap.
- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Reproduction

```simple
val match = [7, 9]
val first = match[0]
```

The pure-Simple parser accepts the G26 keyword binding, then reports
`expected :, got Newline` on `match[0]`. `parse_primary_expr` consumes
`match` as the match-expression introducer because `g33_kw_ident_follow`
does not include `[`, which can also begin a valid match scrutinee.

## Required Fix

Use token adjacency to disambiguate the forms: `match[0]` must remain keyword
identifier postfix indexing, while spaced `match [0]: ...` must remain a match
expression. Add one focused parser regression for both forms. Until then,
Stage 4 sources use non-keyword local names such as `match_result`.

## Evidence

Strict bootstrap checkpoint `f461c1cb248150a116c05b95b42a0ba23b9a218c`
failed in `src/std/nogc_sync_mut/compression/gzip/lz77.spl:105` while parsing
`val distance = match[0]`.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
