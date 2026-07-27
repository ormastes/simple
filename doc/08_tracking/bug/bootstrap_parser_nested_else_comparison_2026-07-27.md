# Bootstrap Parser Rejects Nested Else Comparison

## Status

OPEN. This blocks the full Stage 4 CLI build and therefore blocks deployment of
a current pure-Simple runner.

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

The same function contains earlier nested `if ge < 0:` and `if pe < 0:`
conditions that parse, so this is a context-sensitive bootstrap parser defect,
not unsupported comparison syntax.

## Evidence

- Source commit: `a50016fa75e2`
- Stage 2 SHA-256:
  `5ede8b5598902007ef9d9916e3e8ab427beb6d1f4f319da0810a1a6fee49863a`
- Stage 3 SHA-256:
  `b92db12414a1d7e433f5da580579ed3c59d5c4719db07f6f7e45403ccea0a0b0`
- Stage 4 log:
  `build/bootstrap/cosmos-production-20260727/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`

## Required Fix

Minimize the nested branch into a parser regression fixture, fix the shared
parser path, and verify that fixture before another full bootstrap. Do not
replace the valid source condition with a silent workaround.
