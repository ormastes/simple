# Bootstrap Parser Rejects Address-Of Cast Arguments

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
through the prior indexed-`match` blocker, then fails at
`src/os/userlib/device.spl:26` and four equivalent syscall arguments:

```spl
val info_result = syscall(80, 1, i, &buf as u64, 0, 0)
```

The first diagnostic is:

```text
unexpected token in expression: & '&'
```

The pure-Simple expression parser does not admit `TOK_AMPERSAND`/`&` as the
prefix address-of operator in this argument position, so the subsequent cast
and commas cascade into recovery diagnostics.

## Evidence

- Source commit: `3e68805fb09f`
- Stage 2 SHA-256:
  `1e6cd28941fe12c9ff0ed2097e0ccad24e0fa5af83cf8e9aa78c26b7d438f711`
- Stage 3 SHA-256:
  `fae8d61541d7c5b4d71a63f78cd0984922e9bc5d5576e20773296d4aac8e2558`
- Stage 4 log:
  `build/bootstrap/cosmos-production-20260727/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- First failed source: `src/os/userlib/device.spl:26`
- Equivalent failures: lines 44, 211, 241, and 275.

## Required Fix

Add prefix address-of parsing at the shared unary-expression layer, preserve
binary `&`, verify `&value as u64` inside a call argument with a focused AST
regression, then run one bounded strict bootstrap. Do not rewrite the valid
userlib syscall arguments as a bootstrap workaround.
