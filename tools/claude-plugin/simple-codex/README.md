# simple-codex

Simple language MCP server for Claude Code, providing code intelligence and 50 analysis tools for the Simple compiler ecosystem.

## Tool Categories

| Category | Tools | Description |
|----------|-------|-------------|
| **CLI** | `simple_build`, `simple_test`, `simple_run` | Build, test, and run Simple projects |
| **Analysis** | `simple_check`, `simple_dependencies`, `simple_stats` | Static analysis and project metrics |
| **Code Query** | `simple_ast_query`, `simple_sem_query`, `simple_search` | AST traversal, semantic queries, symbol search |
| **Diagnostics** | `simple_lint`, `simple_doc_coverage` | Linting and documentation coverage |
| **Debug** | `simple_trace`, `simple_profile` | Tracing and profiling |
| **VCS** | `simple_todo_scan`, `simple_bug_add`, `simple_bug_gen` | TODO tracking and bug management |
| **File I/O** | `simple_read`, `simple_write`, `simple_glob` | File operations |

## Key Tools

- `simple_check` — full project check (parse + type + lint)
- `simple_read` — read file contents
- `simple_search` — symbol search across project
- `simple_dependencies` — module dependency graph
- `simple_ast_query` — query AST nodes by type/name
- `simple_sem_query` — semantic queries (types, references)
- `simple_test` — run test suite or single spec file
- `simple_build` — build project (debug or release)

## Installation

### Prerequisites
The Simple compiler binary (`bin/release/simple`) must be built first:

```bash
cd /path/to/simple
cargo build --profile bootstrap -p simple-driver --manifest-path src/compiler_rust/Cargo.toml
bin/simple build --release
```

### Install plugin
Copy the plugin to the Claude Code plugins cache:

```bash
mkdir -p ~/.claude/plugins/cache/simple-codex/simple-codex/local
cp -r tools/claude-plugin/simple-codex/.claude-plugin ~/.claude/plugins/cache/simple-codex/simple-codex/local/
cp tools/claude-plugin/simple-codex/README.md ~/.claude/plugins/cache/simple-codex/simple-codex/local/
```

Then create `~/.claude/plugins/cache/simple-codex/simple-codex/local/.mcp.json` with absolute paths:

```json
{
  "simple-codex": {
    "command": "/absolute/path/to/simple/bin/release/simple",
    "args": ["run", "/absolute/path/to/simple/src/app/mcp/main.spl"]
  }
}
```

### Verify
Restart Claude Code. MCP tools prefixed with `simple_` should be available.

## Architecture

The MCP server runs as a subprocess launched by Claude Code:
- **Protocol:** JSON-RPC 2.0 over stdio (MCP standard)
- **Tool dispatch:** 50 tools across 7 categories, dispatched by name
- **In-process:** All analysis runs in-process via the Simple compiler — no subprocesses

## More Information
- [Simple Language Repository](https://github.com/simple-lang/simple)
- [MCP Specification](https://modelcontextprotocol.io/)
