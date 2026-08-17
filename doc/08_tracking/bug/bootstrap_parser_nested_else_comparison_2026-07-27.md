# Bootstrap Parser Rejects Nested Else Comparison

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

FIXED AND CLEARED IN FULL BOOTSTRAP. The focused parser executable passes, and
the strict Stage 4 retry parsed beyond `pptx_export.spl` and the later
`formula.spl` control-flow cases.

## Reproduction

Run:

```sh
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --full-cli --deploy --no-mcp --jobs=min \
  --output=build/bootstrap/cosmos-production-20260727
```

Stage 2 and Stage 3 pass sanity and provenance. Stage 4 then parses through the
previous Office tuple blockers and fails at
`src/app/office/pptx_export.spl:515`:

```spl
else:
    val ce = _find_at(xml, "</p:pic>", pc)
    if ce < 0:
        scanning = false
```

The first diagnostic is:

```text
expected Ident, got < '<'
```

The lexer classifies `ce` as the computation-expression keyword. The primary
expression parser therefore entered the `ce NAME:` branch unconditionally,
advanced to `<`, and expected a builder identifier. Comparison parsing itself
was not defective.

## Evidence

- Source commit: `a50016fa75e2`
- Stage 2 SHA-256:
  `5ede8b5598902007ef9d9916e3e8ab427beb6d1f4f319da0810a1a6fee49863a`
- Stage 3 SHA-256:
  `b92db12414a1d7e433f5da580579ed3c59d5c4719db07f6f7e45403ccea0a0b0`
- Original Stage 4 log path, later reused by the successful-progress retry:
  `build/bootstrap/cosmos-production-20260727/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- Focused parser executable SHA-256:
  `9a9b97f7c5361280671f6dae100f599229271283868e91478894c620a2b77cc7`
- Focused parser executable result:
  `STATUS: PASS ce-keyword-parser`
- Full-bootstrap source commit: `69c7c0fb7b0a`
- Full-bootstrap result: Stage 4 parsed beyond this source and later stopped at
  the unrelated mixed-ternary defect tracked in
  `bootstrap_parser_then_elif_mixed_ternary_2026-07-27.md`.

## Fix

The shared primary-expression parser now treats `ce` as the computation
expression form only when a builder identifier follows. Otherwise it returns
the existing identifier AST node and lets normal postfix and comparison
parsing continue. A mirrored parser regression covers both `if ce < 0:` and a
valid `ce result:` expression block.

The strict full-bootstrap evidence confirms the source fix. Do not replace the
valid source condition with a workaround.
