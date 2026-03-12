# cmm-lsp

CMM (TRACE32 PRACTICE) language server for Claude Code, providing code intelligence for `.cmm` scripts used in Lauterbach TRACE32 debugger environments.

## Supported Extensions
`.cmm`

## Features

- **Completions** — TRACE32 commands (100+), PRACTICE functions (50+), macro names, with `.`, `&`, `/` triggers
- **Hover** — command and function documentation with syntax descriptions
- **Go to definition** — jump to label and macro definitions
- **Document symbols** — labels and macros as outline symbols
- **Diagnostics** — parse errors, undefined labels/macros, unreachable code, unused macros

## Installation

### Prerequisites
The Simple compiler binary (`bin/release/simple`) must be built first:

```bash
cd /path/to/simple
cargo build --profile bootstrap -p simple-driver --manifest-path src/compiler_rust/Cargo.toml
bin/simple build --release
```

### Install plugin
The Claude Code plugin is a bundle/package, not a separate executable.
It wraps the checked-in `cmm-lsp` entrypoint and lives in the TRACE32 tools
submodule.

Current Claude Code CLI builds install plugins from marketplaces, not from a
local `--dir` path. Use the checked-in marketplace:

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install cmm-lsp@simple-local
```

Release asset:

```text
cmm-lsp-claude-plugin-1.1.1.tar.gz
```

Current limitation:
- the release tarball is not self-contained
- as of March 12, 2026, the latest published T32 release does not include the plugin tarball yet
- the checked-in `.lsp.json` still expects a repo checkout containing `bin/release/simple` and this `cmm_lsp/` source tree

The bundled `.lsp.json` already points at the checked-in CMM LSP entrypoint via
the workspace-relative path `examples/10_tooling/trace32_tools/cmm_lsp/mod.spl --lsp`.
The actual executable/runtime remains `bin/release/simple`.

### Verify
Restart Claude Code and open a `.cmm` file. Hover and completion should work automatically.

## Architecture

The LSP server runs as a subprocess launched by Claude Code:
- **Protocol:** JSON-RPC 2.0 over stdio with Content-Length framing
- **In-process parsing:** CMM lexer, parser, and analyzer run in-process — no subprocesses
- **Command database:** 100+ TRACE32 commands with categories and documentation
- **Function database:** 50+ PRACTICE built-in functions with signatures

## More Information
- [TRACE32 Documentation](https://www.lauterbach.com/frames.html?home.html)
- [LSP Specification](https://microsoft.github.io/language-server-protocol/)
