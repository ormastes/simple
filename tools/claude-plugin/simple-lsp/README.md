# simple-lsp

Simple language server for Claude Code, providing code intelligence and analysis.

## Supported Extensions
`.spl`, `.shs`

## Features
- **Go to definition** — jump to function, class, struct, enum declarations
- **Find references** — locate all usages of a symbol across the project
- **Hover** — type info and documentation at cursor position
- **Completions** — context-aware code completions with `.` and `::` triggers
- **Document symbols** — outline of functions, classes, structs, enums in a file
- **Diagnostics** — error checking on file open and save
- **Signature help** — parameter hints at call sites
- **Document highlight** — same-file reference highlighting
- **Type definition** — jump to where a type is defined
- **Implementation** — find trait implementations
- **Folding ranges** — code folding for blocks and functions

## Installation

### Prerequisites
The Simple compiler binary (`bin/release/simple`) must be built first:

```bash
cd /path/to/simple
# Build using Rust bootstrap
cargo build --profile bootstrap -p simple-driver --manifest-path src/compiler_rust/Cargo.toml
# Then self-host
bin/simple build --release
```

### Install plugin
Copy the plugin to the Claude Code plugins cache:

```bash
mkdir -p ~/.claude/plugins/cache/simple-lsp/simple-lsp/local
cp -r tools/claude-plugin/simple-lsp/.claude-plugin ~/.claude/plugins/cache/simple-lsp/simple-lsp/local/
```

Then create `~/.claude/plugins/cache/simple-lsp/simple-lsp/local/.lsp.json` with absolute paths:

```json
{
  "simple": {
    "command": "/absolute/path/to/simple/bin/release/simple",
    "args": ["run", "/absolute/path/to/simple/src/app/lsp/main.spl"],
    "extensionToLanguage": {
      ".spl": "simple",
      ".shs": "simple"
    },
    "startupTimeout": 30000
  }
}
```

### Verify
Restart Claude Code and open a `.spl` file. Hover and definition should work automatically.

## Architecture

The LSP server runs as a subprocess launched by Claude Code:
- **Protocol:** JSON-RPC 2.0 over stdio with Content-Length framing
- **Fast path:** Lightweight query via `lsp_query.spl` (~100ms, no compiler imports)
- **Heavy path:** Full compiler check via `query.spl` (diagnostics on open/save)

## More Information
- [Simple Language Repository](https://github.com/simple-lang/simple)
- [LSP Specification](https://microsoft.github.io/language-server-protocol/)
