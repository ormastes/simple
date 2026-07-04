# Codebase-MCP Integration Research

**Date:** 2026-07-01  
**Domain:** infra/tooling  
**Keywords:** MCP, RepoMix, code analysis, remote repository packing

## Overview

`codebase-mcp` is a RepoMix-backed MCP server that packs local or remote GitHub repositories into a single structured text output. It provides a standardized MCP interface for code analysis and repository inspection, complementing Simple's native MCP servers for specific use cases.

## What codebase-mcp Does

The implementation is a thin MCP wrapper around RepoMix:

```
MCP client
  → codebase-mcp server (stdio)
    → npx repomix ...
      → packed codebase text
```

### Three Main Tools

| Tool | Purpose |
|------|---------|
| `getCodebase` | Pack a local working directory using RepoMix |
| `getRemoteCodebase` | Pack a remote GitHub repo (`npx repomix --remote <repo>`) |
| `saveCodebase` | Save RepoMix output to a file instead of returning directly |

**Arguments (common):** cwd, output format, file summaries, directory structure, comment/empty-line removal, line numbers, include/ignore patterns.

## Implementation Details

### Architecture
- **CLI wrapper:** `codebase-mcp start` (Node.js entry point)
- **Tool registration:** MCP `tools/list` and `tools/call` flow (standard MCP)
- **RepoMix invocation:** `npx repomix --remote ...` or local `repomix` for local directories
- **Output transport:** MCP tool result (stdout-only)

### Known Issues

1. **Banner Pollution:** The CLI prints `Starting Codebase MCP Server...` via `console.log()` before starting the MCP server. Since MCP requires stdout to contain only JSON-RPC messages, strict MCP clients may fail. Workaround: use the underlying server file directly or patch `console.log` to `console.error`.

2. **Buffer Sizing:** Uses `execSync` with a 50 MB buffer, which can overflow on very large repos or lax formatting.

3. **Shell Injection Risk:** Tool arguments (repo, patterns) are interpolated into shell commands without sanitization. Treat as trusted input only.

## Relationship to Simple's MCP Servers

Simple ships native MCP servers for direct integration:

| Server | Binary | Purpose |
|--------|--------|---------|
| `simple-mcp` | `bin/simple_mcp_server` | Code intelligence, build/test, VCS, search |
| `simple-lsp-mcp` | `bin/simple_lsp_mcp_server` | LSP: diagnostics, completions, hover, goto-def |

**When to use codebase-mcp vs. simple-mcp:**

- **codebase-mcp:** Generic repo inspection, remote GitHub analysis, RepoMix-style packing (language-agnostic)
- **simple-mcp:** Simple-specific operations (compile, test, lint, search), in-process execution, tight IDE/editor integration

## Applying to ormastes/simple

### Scale Considerations

Simple is large: ~15,137 source files, ~2.3M non-comment LOC. A full repo pack via codebase-mcp can hit buffer limits or become unwieldy.

**Recommended:** Use focused `includePatterns` to pack only the MCP-related subset:

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

This covers:
- MCP documentation and configuration
- Simple's MCP server source code
- SDK and registry files
- Minimal examples

### Setup for Local Development

1. **Check out Simple locally:**
   ```bash
   git clone --recurse-submodules https://github.com/ormastes/simple.git
   cd simple
   export PATH="$PWD/bin:$PATH"
   ```

2. **Install MCP config** (regenerates `.mcp.json` for your local paths):
   ```bash
   sh config/mcp/install.shs
   ```

   **Note:** The checked-in `.mcp.json` hardcodes `/home/ormastes/dev/pub/simple`; the install script regenerates it for your machine.

3. **Current workaround:** The install script launches MCP servers from source (`bin/simple run src/app/mcp/main.spl`) because native `simple_mcp_server` binary has stability issues. This may be fixed in future deployments.

## Best Practical Setup (Hybrid)

Use both servers for complementary strengths:

```json
{
  "mcpServers": {
    "codebase-mcp": {
      "command": "node",
      "args": ["/path/to/codebase-mcp/dist/tools/codebase.js"]
    },
    "simple-mcp": {
      "command": "/bin/sh",
      "args": [
        "-lc",
        "cd '/path/to/simple' && exec bin/simple run src/app/mcp/main.spl"
      ],
      "env": {
        "SIMPLE_LOG": "error",
        "RUST_LOG": "error"
      }
    },
    "simple-lsp-mcp": {
      "command": "/bin/sh",
      "args": [
        "-lc",
        "cd '/path/to/simple' && exec bin/simple run src/app/simple_lsp_mcp/main.spl"
      ],
      "env": {
        "SIMPLE_LOG": "error"
      }
    }
  }
}
```

## Security & Reliability Notes

1. **Shell Injection:** `codebase-mcp` builds shell commands from tool arguments with `execSync`. Never expose to untrusted input.

2. **MCP Verification:** Verify with actual MCP `initialize` + `tools/list` + at least one `tools/call`, not just server presence.

3. **Source vs. Native:** For Simple, prefer source-mode launch (`bin/simple run src/app/mcp/main.spl`) until native binary stability improves. Verify with `MCP.md` and repo's own MCP guide.

## Future Directions

- **Native stability:** Fix native `simple_mcp_server` core dumps on real `tools/call` to enable binary launch
- **Buffer management:** Investigate buffer overflow on large repos; consider streaming output
- **Pattern optimization:** Cache RepoMix pattern sets for common use cases (stdlib, compiler, runtime subsets)
