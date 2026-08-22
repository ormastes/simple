# native-build --entry-closure fails with span-less `undefined field 'kind'`

Filed: 2026-08-21
Status: OPEN
Severity: blocker — no MCP or LSP-MCP native artifact can be built from `origin/main`

## Symptom

```
SIMPLE_CACHE_SCOPE=mcp bin/release/x86_64-unknown-linux-gnu/simple native-build \
  --runtime-bundle core-c-bootstrap --source src/app --entry-closure \
  --entry src/app/mcp/main.spl --strip --threads 2 \
  --output build/mcp-sanity/simple_mcp_server
```

fails after ~1972 s with exactly one error:

```
error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
error: native-build worker exited with code 1
```

The sibling entry `src/app/simple_lsp_mcp/main.spl` fails identically (~435 s).
`src/app/simple_lsp_mcp/**` contains **no** `.kind` access at all, so the defect
is in shared code reached through the entry closure, or in the driver itself.

## Why it is hard to diagnose (three separate defects)

1. **The diagnostic has no file/line span.** It is the only error emitted. Every
   other diagnostic in the same stream carries a `--> path:line:col`.
2. **It fires after every instrumented source reports clean.** The line
   immediately preceding it is
   `[bootstrap-error-count] source_idx=2 point=post-store count=0`, with
   `count=0` at all four points for all three sources. So this is not an
   ordinary source-compile error; it is on the post-store entry-closure /
   codegen path.
3. **The driver truncates worker stderr from the middle** — "TRUNCATED: 16945 of
   28945 bytes of worker stderr were dropped from the MIDDLE" — discarding
   whatever context would localize it.

## Evidence

- Full preserved stderr: `/mnt/data/tmp/native-build-stderr-359022.log`
  (MCP entry) and `/mnt/data/tmp/native-build-stderr-321437.log` (LSP entry);
  the error is at line 806 in the latter.

## Relationship to the fixed blocker

This is the *next* wall past the HIR-lowering failure in
`src/lib/common/text_advanced.spl` fixed by `5c285c2436f`. Before that fix the
build never reached this point. The `text_advanced` diagnostics are confirmed
absent from post-fix build logs.

## Fix directions

- Attach a span to the `undefined field` diagnostic — worth doing regardless,
  since it blocks localization of this and every future instance.
- Stop truncating worker stderr from the middle, or preserve all `error:` lines
  (the driver already has a "PRESERVED DIAGNOSTICS" mechanism; it preserved
  only 2 lines here).
- Locate the unguarded `.kind` read on a nil receiver on the post-store
  entry-closure path.

## Repro cost

~33 min per attempt for the MCP entry, ~7 min for the LSP entry; prefer the LSP
entry for iteration.
