# query_visibility workspace-symbols: hidden-symbol summary vs `[]` oracle — needs owner decision

- **Date:** 2026-11-12
- **Status:** OPEN — needs-decision (spec oracle vs intended product behavior)
- **Severity:** Low-Medium (behavioral contract of a shipped LSP/MCP surface)
- **Area:** `src/app/cli/query_visibility.spl` (workspace-symbols), spec `test/02_integration/app/query_visibility_workspace_symbols_spec.spl`

## Evidence

The spec's second example pins:

```simple
val (stdout, stderr, code) = simple_cli_run(
    ["src/app/cli/query_visibility.spl", "workspace-symbols", "--query", "query_visibility",
     "--requester", "src/lib/nogc_sync_mut/lsp/main.spl"], 120000)
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("[]")
```

Actual product behavior returns a single structured "hidden symbols summary"
object instead of `[]` when every match is boundary-private, e.g.:

```json
[{"name":"⋯ 11 hidden (11 module_private fn) — reveal: lsp_symbols visibility=\"all\"; ...",
  "kind":1,
  "detail":"hidden symbols summary; visibility=public",
  "simpleHiddenSummary":{"hidden":11,"by_class":{"module_private":11}, ...}}]
```

The summary is clearly an intentional feature (it carries reveal instructions
for MCP, LSP initializationOptions, and the `simple.setVisibility`
executeCommand), i.e. the spec's `[]` expectation predates the feature.

## Decision needed

Either:

1. The feature is correct and the spec oracle is stale → update the spec to
   expect the summary object (and the first/third examples' expectations to
   the current metadata shape); or
2. The summary should only appear when the caller asks for it and a plain
   cross-boundary request should return `[]` → product change in
   `query_visibility.spl`.

## Note

This spec also asserts `stderr == ""` on spawned `bin/simple` runs, which the
Rust seed can never satisfy (compile-warning banner). Under the phase-2 seed
environment the file cannot go fully green either way; the decision above
should be executed and verified under the self-hosted binary.
