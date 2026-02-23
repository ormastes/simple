# Application Layer (`src/app/`)

All applications and libraries are written in pure Simple (`.spl` files). They run as subcommands of the single `bin/simple` binary via the CLI dispatch table (`src/app/cli/dispatch/table.spl`).

## Usage

```bash
bin/simple <command> [options]
```

## CLI Subcommands

Registered in the dispatch table. Each maps to `src/app/<module>/main.spl`.

### Compilation

| Command | Module | Description |
|---------|--------|-------------|
| `compile` | `compile/` | Compile `.spl` source files |
| `targets` | `targets/` | List supported compilation targets |
| `linkers` | `linkers/` | List available linkers |

### Build & Run

| Command | Module | Description |
|---------|--------|-------------|
| `build` | `build/` | Build orchestration (compile, test, lint, fmt) |
| `run` | `run/` | Build and run a program |
| `bench` | — | Benchmark runner |
| `clean` | — | Clean build artifacts |

### Testing

| Command | Module | Description |
|---------|--------|-------------|
| `test` | `test/` | Test runner (delegates to runtime) |

### Code Quality

| Command | Module | Description |
|---------|--------|-------------|
| `lint` | `lint/` | Linter |
| `fix` | `fix/` | Auto-fix code issues |
| `fmt` | `formatter/` | Code formatter |
| `check` | `check/` | Run all quality checks |
| `check-capsule` | `cli/` | Capsule visibility checks |
| `check-dbs` | `cli/` | Validate databases |
| `fix-dbs` | `cli/` | Repair databases |
| `duplicate-check` | `duplicate_check/` | Detect code duplication |
| `verify` | `verify/` | Code verification |
| `qualify-ignore` | `qualify_ignore/` | Qualification ignore rules |

### Analysis & Query

| Command | Module | Description |
|---------|--------|-------------|
| `query` | `query/` | Query the codebase |
| `info` | `info/` | Show project/module info |
| `spec-coverage` | `spec_coverage/` | Spec coverage analysis |
| `replay` | `replay/` | Replay execution traces |
| `diff` | `diff/` | Diff tool |
| `context` | `context/` | Context/scope inspection |
| `constr` | `constr/` | Constraint checking |

### Code Generation & Docs

| Command | Module | Description |
|---------|--------|-------------|
| `gen-lean` | `gen_lean/` | Generate Lean proofs |
| `feature-gen` | `feature_gen/` | Generate feature docs from tests |
| `feature-doc` | `feature_doc/` | Feature documentation |
| `spec-gen` | `spec_gen/` | Generate spec files |
| `sspec-docgen` | `sspec_docgen/` | Generate docs from SSpec tests |
| `todo-scan` | `todo_scan/` | Scan TODOs in codebase |
| `todo-gen` | `todo_gen/` | Generate TODO report |
| `wrapper-gen` | `wrapper_gen/` | Generate FFI wrappers |
| `ffi-gen` | `ffi_gen/` | Generate FFI bindings |

### Package Management

| Command | Module | Description |
|---------|--------|-------------|
| `init` | `init/` | Initialize a new project |
| `install` | `install/` | Install dependencies |
| `publish` | `publish/` | Publish a package |
| `add` | `add/` | Add a dependency |
| `remove` | `remove/` | Remove a dependency |
| `search` | `search/` | Search package registry |
| `list` | `list/` | List installed packages |
| `tree` | `tree/` | Show dependency tree |

### Documentation & Dashboard

| Command | Module | Description |
|---------|--------|-------------|
| `brief` | `brief/` | Brief project summary |
| `dashboard` | `dashboard/` | Terminal dashboard |

### Bug Tracking

| Command | Module | Description |
|---------|--------|-------------|
| `bug-add` | — | Add a bug report |
| `bug-gen` | — | Generate bug report |

### Other

| Command | Module | Description |
|---------|--------|-------------|
| `repl` | `repl/` | Interactive REPL |
| `watch` | `watch/` | File watcher with rebuild |
| `mcp` | `mcp/` | MCP server for AI integration |
| `web` | `web/` | Web framework server |
| `i18n` | `i18n/` | Internationalization |
| `migrate` | `migrate/` | Code migration tool |

## Libraries (not direct subcommands)

These modules provide shared infrastructure used by the subcommands above.

> **Note:** CLI argument parsing (`cli_parser`), CLI utilities (`cli_util`), and package helpers (`package_utils`) have moved to `src/lib/cli/`. Import via `lib.cli.*`.

| Module | Purpose |
|--------|---------|
| `io/` | SFFI I/O wrappers (file, process, env) |
| `cli/` | CLI dispatch, arg parsing, entrypoints |
| `desugar/` | AST desugaring transforms |
| `test_runner_new/` | SSpec test framework runner |
| `test_analysis/` | Test result analysis |
| `package/` | Package management core (semver, manifest, lockfile) |
| `package.registry/` | Package registry client |
| `parser/` | Parser loading infrastructure |
| `depgraph/` | Dependency graph analysis |
| `stats/` | Codebase statistics |
| `cache/` | Caching layer |
| `env/` | Environment abstraction |
| `gc/` | Garbage collection interface |
| `lock/` | Lock file handling |
| `profiling/` | Profiling support |
| `perf/` | Performance utilities |
| `debug/` | Debugging support |
| `protocol/` | Protocol abstractions (JSON-RPC) |
| `utils/` | General utilities |
| `src/` | Source file utilities |
| `sdn/` | SDN format parser/writer |
| `coverage/` | Code coverage |
| `spl_coverage/` | Simple-level coverage |
| `audit/` | Security/dependency audit |
| `grammar_doc/` | Grammar documentation |
| `linker_gen/` | Linker script generation |
| `stub/` | Stub generation |
| `tooling/` | Shared tooling infra |
| `exp/` | Experimental features |
| `leak_finder/` | Memory leak detection |

### Dev Tool Servers (separate processes, same binary)

| Module | Purpose |
|--------|---------|
| `lsp/` + `lsp.handlers/` | Language Server Protocol |
| `dap/` | Debug Adapter Protocol |
| `mcp/` | MCP server for Simple |
| `mcp_jj/` | MCP server for jj VCS |

### Editor & Platform Integration

| Module | Purpose |
|--------|---------|
| `nvim_plugin/` | Neovim plugin |
| `vscode_extension/` | VS Code extension |
| `unreal_cli/` | Unreal Engine integration |

### LLM Integration

| Module | Purpose |
|--------|---------|
| `llm_caret/` | LLM caret (`^`) integration |
| `lms/` | LLM service layer |
| `lms_simple/` | Simple-specific LLM support |

### Dashboard (web)

| Module | Purpose |
|--------|---------|
| `dashboard/` | Terminal dashboard |
| `dashboard.render/` | Dashboard rendering |
| `dashboard.views/` | Dashboard view components |
| `web_dashboard/` | Web-based dashboard |
| `web_dashboard.api/` | Web dashboard API |
| `web_dashboard.static/` | Web dashboard static assets |

### Infrastructure

| Module | Purpose |
|--------|---------|
| `vm/` | QEMU VM management |
| `semihost/` | Semihosting support |
| `ci/` | CI integration |
| `release/` | Release process automation |
| `setup/` | Project setup |
| `update/` | Self-update mechanism |
| `vcs/` + `jj/` | Version control integration |
| `diagram/` | Diagram generation |
| `doc/` | Documentation utilities |
| `task/` + `task_gen/` | Task management |

## Architecture

All subcommands are dispatched through a single entry point:

```
bin/simple <cmd> [args...]
    -> src/app/cli/main.spl
    -> src/app/cli/dispatch.spl (find_command + dispatch_command)
    -> src/app/cli/dispatch/table.spl (50 command entries)
    -> src/app/<module>/main.spl
```

Each `CommandEntry` has:
- `name` — CLI command name
- `app_path` — path to the Simple implementation
- `env_override` — env var to force Rust fallback (legacy, unused)
- `needs_rust_flags` — flags that require Rust fallback (legacy)
