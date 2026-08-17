# Bootstrap Parser Rejects Indexed Match Identifier

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

FIXED AND CLEARED IN FULL BOOTSTRAP. The focused AST regression covers both
expression and statement indexing plus spaced array-scrutinee match syntax, and
the strict Stage 4 retry parsed beyond `lz77.spl`.

## Reproduction

Run:

```sh
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --full-cli --deploy --no-mcp --jobs=min \
  --output=build/bootstrap/cosmos-production-20260727
```

Stage 2 and Stage 3 pass sanity, capability, and provenance. Stage 4 parses
through the prior ternary blocker, then fails at
`src/std/nogc_sync_mut/compression/gzip/lz77.spl:105`:

```spl
val match = lz77_find_match(data, pos, window_start, max_len)
val distance = match[0]
val length = match[1]
```

The first diagnostic is:

```text
expected :, got Newline ''
```

`match` lexes as `TOK_KW_MATCH`. The primary parser already has a
keyword-as-identifier fallback, but `g33_kw_ident_follow` does not classify `[`
as an identifier continuation. It therefore routes `match[0]` into
match-expression parsing and expects a match-arm colon.

## Evidence

- Source commit: `1f27b9be2cb7`
- Stage 2 SHA-256:
  `0a7542e6edad3924a8c91f90718768e7be072efe0f98d4b96043931f99208775`
- Stage 3 SHA-256:
  `8503a25336aaa906e0edc91f91dea440a4e122402ac8d34853378c052d49242e`
- Original Stage 4 log path, later reused by the successful-progress retry:
  `build/bootstrap/cosmos-production-20260727/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- First failed source:
  `src/std/nogc_sync_mut/compression/gzip/lz77.spl:105`

## Fix

The statement and primary-expression parsers now use token adjacency to
distinguish `match[0]` from whitespace-separated `match [array]:`. This
preserves real match syntax while allowing the keyword-named local.

The strict retry at source commit `3e68805fb09f` cleared this source and later
stopped at the unrelated prefix address-of defect tracked in
`bootstrap_parser_address_of_cast_2026-07-27.md`.
