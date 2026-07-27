# Bootstrap Parser Rejects Indexed Match Identifier

## Status

OPEN. This blocks the full Stage 4 CLI build and deployment of a current
pure-Simple runner.

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
- Stage 4 log:
  `build/bootstrap/cosmos-production-20260727/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- First failed source:
  `src/std/nogc_sync_mut/compression/gzip/lz77.spl:105`

## Required Fix

Extend the shared keyword-identifier follow predicate to admit indexing,
add one focused AST regression for `match[0]` while preserving value-level
`match`, then run one bounded strict bootstrap. Do not rename the valid source
variable as a bootstrap workaround.
