# Bootstrap Parser Rejects Mixed Then/Elif Ternary

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

FIXED AND CLEARED IN FULL BOOTSTRAP. The focused nested-AST regression passes,
and the strict Stage 4 retry parsed beyond `md_renderer.spl`.

## Reproduction

Run:

```sh
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --full-cli --deploy --no-mcp --jobs=min \
  --output=build/bootstrap/cosmos-production-20260727
```

Stage 2 and Stage 3 pass sanity, capability, and provenance. Stage 4 parses
through the prior `ce` comparison, multiline inline-if, and comma-grouped match
blockers, then fails at `src/std/editor/render/md_renderer.spl:233`:

```spl
val tag = if level == 4 then "heading_4" elif level == 5 then "heading_5" else: "heading_6"
```

The first diagnostic is:

```text
unexpected token in expression: : ':'
```

The pure-Simple ternary parser accepts `if C then X else Y`, but its `then`
branch handles only `else`; it does not consume an `elif ... then ...` chain.

## Evidence

- Source commit: `69c7c0fb7b0a`
- Stage 2 SHA-256:
  `352fbc3e0792040eac66537dffe5ebf32c67020c3875285bfb87d58bb8201c0e`
- Stage 3 SHA-256:
  `a4981e84304111d6aa65140a6f59401ff2f9e652c3b12020f7a869cd9c54e42b`
- Original Stage 4 log path, later reused by the successful-progress retry:
  `build/bootstrap/cosmos-production-20260727/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- First failed source: `src/std/editor/render/md_renderer.spl:233`

## Fix

The shared expression-level ternary parser now recurses on `elif` exactly as
the colon form and Rust authority do. The focused regression verifies that the
else branch is a nested `EXPR_IF`.

The strict retry at source commit `1f27b9be2cb7` cleared this source and later
stopped at the unrelated `match[0]` keyword-identifier defect tracked in
`bootstrap_parser_match_keyword_identifier_2026-07-27.md`.
