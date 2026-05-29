# LSP Plugin Audit — Simple and CMM

**Date:** 2026-03-12
**Status:** Audit complete

## Summary

The LSP-plugin approach is the correct direction for minimizing token usage.
Using Claude Code's native LSP tool is fundamentally better than routing code
intelligence through MCP query tools.

The current problems are packaging and installation boundaries, not the LSP
approach itself.

## Findings

### 1. Simple plugin is not actually shipped

The repo has no checked-in `tools/claude-plugin/simple-lsp/` bundle.

Current state:
- `tools/claude-plugin/` only contains `simple-codex/.mcp.json`
- `src/lib/nogc_sync_mut/lsp/main.spl` still prints install instructions for
  `tools/claude-plugin/simple-lsp`
- `doc/01_research/simple_lsp_plugin_2026-03-11.md` describes the plugin as if it
  already exists

Conclusion:
- The Simple LSP server exists
- The Simple Claude plugin package does not

### 2. CMM plugin exists, but the released plugin tarball is not standalone

The checked-in CMM plugin bundle exists at:
- `examples/10_tooling/trace32_tools/claude-plugin/cmm-lsp/.claude-plugin/plugin.json`
- `examples/10_tooling/trace32_tools/claude-plugin/cmm-lsp/.lsp.json`

But `.lsp.json` launches:

```json
["bin/simple", "examples/10_tooling/trace32_tools/cmm_lsp/mod.spl", "--lsp"]
```

This is valid inside a source checkout.

It is not a standalone released plugin package, because the release tarball
does not contain:
- `bin/simple`
- `examples/10_tooling/trace32_tools/cmm_lsp/mod.spl`

Conclusion:
- In-repo plugin bundle: valid
- Released plugin tarball: not self-contained

### 3. `simple lsp` is not currently a stable packaged entrypoint

In this checkout:
- `bin/simple run src/lib/nogc_sync_mut/lsp/main.spl --help` works
- `bin/simple lsp --help` fails with `lsp app not found`

Conclusion:
- The planned plugin command from the earlier research note,
  `["bin/simple", "lsp"]`, is not currently reliable in this repo
- Any future Simple plugin should target a verified entrypoint, not the planned
  one

### 4. The fundamental architecture is right

For token minimization, LSP is the right boundary:
- navigation stays in the editor/LSP tool
- diagnostics become automatic
- MCP tool count stays smaller
- prompts do not need to carry navigation/query tool descriptions repeatedly

So the approach is not fundamentally wrong.

The wrong part is mixing two packaging models:
- dev plugin bundle inside a source checkout
- released standalone plugin package

Those need different commands.

## Recommended packaging model

### Dev bundle inside repo

Keep a repo-local plugin bundle for development:
- command may point at workspace-relative sources
- example: `bin/simple run .../mod.spl --lsp`

This is acceptable for contributors working in this checkout.

### Release bundle

Release bundles should point at shipped executables only:
- `cmm-lsp`
- `simple-lsp`

A released plugin tarball should not depend on source-tree paths that are not
inside the tarball.

## Recommended next steps

### CMM

Choose one:

1. Keep shipping the current plugin bundle only as an in-repo/dev install path
   and stop presenting the tarball as standalone.
2. Or patch the release-time `.lsp.json` to launch `cmm-lsp` instead of the
   repo-relative Simple script path.

### Simple

Do not claim the Simple Claude plugin exists until both are true:
- `tools/claude-plugin/simple-lsp/` is checked in
- the plugin command points at a verified entrypoint that actually works in this
  checkout

## Bottom line

- CMM plugin: real, but currently only correct as an in-repo plugin bundle
- Simple plugin: planned, not shipped
- LSP for token minimization: correct approach
- Standalone plugin release packaging: currently inconsistent
