# Codebase-MCP Integration Research

**Date:** 2026-07-01
**Domain:** infra/tooling
**Keywords:** MCP, RepoMix, code analysis, remote repository packing

## Overview

`codebase-mcp` is a RepoMix-backed MCP server that packs local or remote GitHub
repositories into a single structured text output. It provides a standardized
MCP interface for code analysis and repository inspection, complementing
Simple's native MCP servers for specific use cases.

## What codebase-mcp Does

The implementation is a thin MCP wrapper around RepoMix:

```text
MCP client
  -> codebase-mcp server (stdio)
    -> npx repomix ...
      -> packed codebase text
```

### Three Main Tools

| Tool | Purpose |
|------|---------|
| `getCodebase` | Pack a local working directory using RepoMix |
| `getRemoteCodebase` | Pack a remote GitHub repo (`npx repomix --remote <repo>`) |
| `saveCodebase` | Save RepoMix output to a file instead of returning directly |

Common arguments include cwd, output format, file summaries, directory
structure, comment/empty-line removal, line numbers, include patterns, and
ignore patterns.

## Implementation Details

- CLI wrapper: `codebase-mcp start` through a Node.js entry point.
- Tool registration: standard MCP `tools/list` and `tools/call`.
- RepoMix invocation: `npx repomix --remote ...` or local `repomix`.
- Output transport: MCP tool result.

Known issues:

- Banner pollution: startup banners on stdout can break strict MCP clients.
- Buffer sizing: `execSync` with a 50 MB buffer can overflow on large repos.
- Shell injection risk: shell-string command construction must be treated as
  trusted-input only.

## Relationship to Simple's MCP Servers

Simple ships native MCP servers for direct integration:

| Server | Binary | Purpose |
|--------|--------|---------|
| `simple-mcp` | `bin/simple_mcp_server` | Code intelligence, build/test, VCS, search |
| `simple-lsp-mcp` | `bin/simple_lsp_mcp_server` | LSP diagnostics, completions, hover, goto-def |

Use `codebase-mcp` for generic repo inspection, remote GitHub analysis, and
RepoMix-style packing. Use `simple-mcp` for Simple-specific operations,
in-process execution, and IDE/editor integration.

## SPipe MCP Integration

SPipe MCP provides codebase-MCP style pack/search/get behavior without adding a
second codebase server.

- `spipe_codebase_profile` returns focused Simple include/ignore patterns.
- `spipe_codebase_pack` runs RepoMix with a fixed argv vector through
  `process_run_timeout`, ingests stdout, and returns status plus byte count.
- `spipe_codebase_ingest`, `spipe_codebase_search`, `spipe_codebase_get`, and
  `spipe_codebase_save` reuse the SPipe tree context store.

The pack command does not stream packed source through the MCP response.
Callers search or fetch the stored rendered tree after ingestion.

## Applying to ormastes/simple

Simple is large: roughly 15k source files and more than 2M non-comment LOC. A
full repo pack can hit buffer limits or become unwieldy. Use focused
`includePatterns` for MCP-related subsets:

```json
{
  "repo": "https://github.com/ormastes/simple",
  "format": "markdown",
  "includeFileSummary": true,
  "includeDirectoryStructure": true,
  "removeEmptyLines": true,
  "showLineNumbers": true,
  "includePatterns": "MCP.md,.mcp.json,config/mcp/**,src/app/mcp/**,src/app/simple_lsp_mcp/**,src/lib/nogc_sync_mut/mcp_sdk/**,examples/10_tooling/minimal_mcp/**,tools/mcp-registry/**,.claude/**",
  "ignorePatterns": ".git/**,.cache/**,target/**,build/**"
}
```

## Best Practical Setup

Use both servers for complementary strengths. For Simple, prefer source-mode
launch until native binary stability is verified:

```json
{
  "mcpServers": {
    "codebase-mcp": {
      "command": "node",
      "args": ["/path/to/codebase-mcp/dist/tools/codebase.js"]
    },
    "simple-mcp": {
      "command": "/bin/sh",
      "args": ["-lc", "cd '/path/to/simple' && exec bin/simple run src/app/mcp/main.spl"],
      "env": {"SIMPLE_LOG": "error", "RUST_LOG": "error"}
    },
    "simple-lsp-mcp": {
      "command": "/bin/sh",
      "args": ["-lc", "cd '/path/to/simple' && exec bin/simple run src/app/simple_lsp_mcp/main.spl"],
      "env": {"SIMPLE_LOG": "error"}
    }
  }
}
```

## Checks

- `bin/release/simple test test/01_unit/lib/nogc_sync_mut/spipe/codebase_ingest_spec.spl --mode=interpreter`
- `bin/release/simple run src/app/spipe_mcp/main.spl codebase-profile`

## Non-goals

No shell-string execution, filesystem write API, or new indexing backend is
added. Those stay app-owned or reuse existing context SQL helpers.
