# CLI / MCP Alignment Matrix

**Date:** 2026-03-27
**Requirement:** doc/02_requirements/feature/simple_cli_mcp_completeness.md
**Plan:** doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md

## Workflow Mapping

### CLI-First Workflows

These workflows are primarily designed for CLI use. MCP equivalents exist as wrappers.

| Workflow | CLI Command | MCP Tool | MCP Type | Notes |
|----------|-------------|----------|----------|-------|
| Build | `simple build` | `simple_build` | Wrapper | CLI has full flag surface |
| Test | `simple test` | `simple_test` | Wrapper | CLI has `--list`, `--only-slow` |
| Lint | `simple build lint` | `simple_lint` | Wrapper | Subcommand of build |
| Format | `simple build fmt` | `simple_format` | Wrapper | Subcommand of build |
| Fix | `simple fix` | `simple_fix` | Wrapper | CLI has `--dry-run` |
| Doc coverage | `simple doc-coverage` | `simple_doc_coverage` | Wrapper | CLI has `--format`, `--missing` |
| Check | `simple build check` | `simple_check` | Wrapper | Full quality checks |

### MCP-First Workflows

These workflows are designed for MCP (LLM/agent) use. No direct CLI equivalent.

| Workflow | MCP Tool | CLI Equivalent | Notes |
|----------|----------|----------------|-------|
| Structured multi-edit | `simple_multi_edit` | None | JSON-structured file edits |
| Debug session management | `debug_create_session` | None | DAP session lifecycle |
| Debug stepping | `debug_step`, `debug_continue` | None | Interactive debug |
| Debug breakpoints | `debug_set_breakpoint` | None | Programmatic breakpoint management |
| Debug evaluation | `debug_evaluate` | None | Expression evaluation in context |
| Debug data breakpoints | `debug_set_data_breakpoint` | None | Hardware watchpoints |
| Debug trace capture | `debug_trace_capture` | None | Trace recording |
| Debug coverage | `debug_coverage_collect` | None | Code coverage collection |
| Debug flash | `debug_flash_program` | None | Embedded firmware flashing |
| Debug PRACTICE scripts | `debug_practice_script` | None | TRACE32 automation |
| Debug OpenOCD monitor | `debug_openocd_monitor` | None | OpenOCD direct commands |
| Debug log management | `debug_log_*` (6 tools) | None | Structured debug logging |
| Task management | `task_list/status/cancel` | None | Background task tracking |
| Test daemon | `test_daemon_*` (4 tools) | `simple test-daemon` | CLI starts daemon, MCP orchestrates |
| Resource browsing | `resources/list`, `resources/read` | None | MCP protocol feature |
| Prompt templates | `prompts/list`, `prompts/get` | None | MCP protocol feature |
| Completions | `completions/complete` | None | MCP protocol feature |

### Dual-Surface Workflows

These workflows have meaningful implementations on both surfaces.

| Workflow | CLI Command | MCP Tool | Semantics Match | Notes |
|----------|-------------|----------|-----------------|-------|
| Read file | `simple <file>` (run) | `simple_read` | Partial | CLI executes, MCP reads content |
| Status | `simple build check` | `simple_status` | Yes | Project health |
| Symbols | `simple query symbols` | `simple_symbols` | Yes | Symbol listing |
| Diagnostics | `simple build lint` | `simple_diagnostics` | Partial | MCP returns structured JSON |
| Run | `simple run` | `simple_run` | Yes | Execute file |
| Diff | `simple diff` | `simple_diff` | Yes | VCS diff |
| API surface | `simple query api` | `simple_api` | Yes | Public API listing |
| API diff | `simple query api-diff` | `simple_api_diff` | Yes | API change detection |
| Dependencies | `simple query deps` | `simple_dependencies` | Yes | Dependency graph |
| Search | `simple query search` | `simple_search` | Yes | Code search |
| AST query | `simple query ast` | `simple_ast_query` | Yes | AST inspection |
| Semantic query | `simple query sem` | `simple_sem_query` | Yes | Semantic analysis |
| Context | `simple query context` | `simple_context` | Yes | Module context |
| Schema query | `simple query schema` | `simple_query_schema` | Yes | Type schema |
| VCS log | `jj log` (external) | `simple_log` | Yes | Commit history |
| VCS new | `jj new` (external) | `simple_new` | Yes | New change |
| VCS commit | `jj commit` (external) | `simple_commit` | Yes | Commit |
| VCS push | `jj git push` (external) | `simple_push` | Yes | Push |
| VCS squash | `jj squash` (external) | `simple_squash` | Yes | Squash changes |
| VCS rebase | `jj rebase` (external) | `simple_rebase` | Yes | Rebase |
| VCS pull | `jj git fetch` (external) | `simple_pull` | Yes | Fetch + rebase |

## CLI-Only Features

| Feature | CLI Command | Notes |
|---------|-------------|-------|
| Version | `simple --version` | Trivial, not needed in MCP |
| Help | `simple --help` | Trivial, MCP has tools/list |
| Compile | `simple compile` | Build workflow covers this |
| Targets | `simple targets` | Build info |
| Linkers | `simple linkers` | Build info |
| Web | `simple web` | Dev server |
| Watch | `simple watch` | File watcher |
| Lex | `simple lex` | Token debugging |
| Grammar doc | `simple grammar-doc` | Grammar documentation |
| Spec coverage | `simple spec-coverage` | Test coverage analysis |
| Feature gen | `simple feature-gen` | Feature doc generation |
| Task gen | `simple task-gen` | Task generation |
| Spec gen | `simple spec-gen` | Test generation |
| SPipe docgen | `simple spipe-docgen` | SPipe documentation |
| Feature doc | `simple feature-doc` | Feature documentation |
| TODO scan | `simple todo-scan` | TODO tracking |
| Stats | `simple stats` | Project statistics |
| Dashboard | `simple dashboard` | TUI dashboard |
| Desugar | `simple desugar` | Syntax desugaring |
| Diagram | `simple diagram` | Diagram generation |
| Package mgmt | `init/add/remove/install/update/list/tree/cache/env/lock` | Full package management |
| i18n | `simple i18n` | Internationalization |
| Info | `simple info` | Project info |
| Brief | `simple brief` | Project summary |
| FFI gen | `simple ffi-gen` | FFI wrapper generation |
| Leak check | `simple leak-check` | Memory leak detection |
| Duplicate check | `simple duplicate-check` | Code duplication |
| Check arch | `simple check-arch` | Architecture checks |
| Check/fix DBs | `simple check-dbs/fix-dbs` | Database checks |

## MCP-Only Features

| Feature | MCP Tool/Method | Notes |
|---------|-----------------|-------|
| Multi-edit | `simple_multi_edit` | Structured JSON edits |
| Debug (25 tools) | `debug_*` | Full DAP/GDB/OpenOCD lifecycle |
| Debug log (6 tools) | `debug_log_*` | Structured debug logging |
| Task management (3 tools) | `task_*` | Background task tracking |
| Resources | `resources/list`, `resources/read` | Protocol feature |
| Prompts | `prompts/list`, `prompts/get` | Protocol feature |
| Completions | `completions/complete` | Protocol feature |
| Roots | `roots/list` | Protocol feature |
| Logging control | `logging/setLevel` | Protocol feature |

## Intentional Divergences

| Area | CLI Behavior | MCP Behavior | Reason |
|------|-------------|--------------|--------|
| File execution | `simple file.spl` runs file | `simple_read` returns content | MCP agents read, not execute |
| Diagnostics | `lint` returns text output | `simple_diagnostics` returns structured JSON | MCP needs structured data |
| Error output | stderr text | JSON error in MCP result | Protocol requirement |
| Exit codes | Process exit code | `isError` field in response | Protocol requirement |
| Multi-edit | Edit single file via CLI | Batch JSON edits | Agent workflow optimization |
| Debug | No CLI debug interface | Full DAP lifecycle | Debug requires state management |
