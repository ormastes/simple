# Project File Manifest

This file declares allowed entries at the project root and links to child
manifests. The workspace root guard (`scripts/check-workspace-root-guard.shs`)
enforces these declarations. Only entries listed here (and in linked child
FILE.md files) are allowed.

## Root Files

| File/Directory | Description |
|---|---|
| `FILE.md` | This manifest |
| `CLAUDE.md` | Claude Code project instructions |
| `README.md` | Project readme |
| `AGENTS.md` | Agent definitions |
| `GEMINI.md` | Gemini instructions |
| `MCP.md` | MCP server documentation |
| `CHANGELOG.md` | Release changelog |
| `VERSION` | Current version |
| `LICENSE` | License file |
| `THIRD_PARTY_NOTICES.md` | Third-party notices |
| `.gitignore` | Git ignore rules |
| `.jjignore` | Jujutsu ignore rules |
| `.gitmodules` | Git submodule definitions |
| `.gitattributes` | Git attributes |
| `.envrc` | direnv configuration |
| `.mcp.json` | MCP server config |
| `.jscpd.json` | Copy-paste detector config |
| `.dockerignore` | Docker ignore rules |
| `bin` | Executables and wrappers |
| `src` | Source code |
| `test` | Test files |
| `examples` | Example projects |
| `doc` | Documentation |
| `config` | Configuration files |
| `scripts` | Build and utility scripts |
| `tools` | Developer tooling |
| `.claude` | Claude Code settings and agents |
| `.codex` | Codex settings |
| `.agents` | Agent definitions |
| `.gemini` | Gemini settings |
| `.github` | GitHub workflows and config |
| `.spipe` | SPipe state files |
| `.simple` | Simple language config |
| `.vscode` | VS Code settings |
| `build` | Build output (mutable, includes target/ and bootstrap/) |
| `tmp` | Temporary files (mutable) |

**No other files at root.**

## Child Manifests

| Path | Enforces |
|---|---|
| `src/FILE.md` | `src/` directory |
| `doc/FILE.md` | `doc/` directory |
| `config/FILE.md` | `config/` directory |
| `scripts/FILE.md` | `scripts/` directory |
| `test/FILE.md` | `test/` directory |
| `bin/FILE.md` | `bin/` directory |

## src/

| Entry | Description |
|---|---|
| `src/app` | Applications (cli, build, mcp, test_runner, etc.) |
| `src/compiler` | Unified compiler (numbered layers 00-99) |
| `src/compiler_rust` | Rust seed compiler and vendor |
| `src/generated` | Generated source files |
| `src/lib` | Standard library (`use std.X`) |
| `src/os` | OS-specific code |
| `src/runtime` | Native runtime and support libraries |
| `src/std` | Standard library aliases |
| `src/tooling` | Compiler tooling |
| `src/type` | Type system definitions |
| `src/unit` | Unit definitions |
| `src/verification` | Formal verification |
| `src/FILE.md` | Source manifest |

## doc/

| Entry | Description |
|---|---|
| `doc/00_llm_process` | LLM process docs |
| `doc/01_research` | Research docs |
| `doc/02_requirements` | Requirements and features |
| `doc/03_plan` | Planning docs |
| `doc/04_architecture` | Architecture docs |
| `doc/05_design` | Design docs |
| `doc/06_spec` | Specifications |
| `doc/07_guide` | Guides and references |
| `doc/08_tracking` | Tracking (tests, todos, bugs) |
| `doc/09_report` | Reports |
| `doc/10_metrics` | Metrics |
| `doc/11_archive` | Archived docs |
| `doc/.obsidian` | Obsidian vault config |
| `doc/README.md` | Doc readme |
| `doc/test` | Doc test files |
| `doc/TODO.md` | TODO tracking |
| `doc/FILE.md` | Doc manifest |

## config/

| Entry | Description |
|---|---|
| `config/bootstrap.sdn` | Bootstrap config |
| `config/critical_files.sdn` | Critical file guard config |
| `config/di.sdn` | Dependency injection config |
| `config/dl.config.sdn` | Deep learning config |
| `config/doc_coverage.sdn` | Doc coverage config |
| `config/docker-compose.test.yml` | Docker test compose |
| `config/docker-compose.yml` | Docker compose |
| `config/mcp` | MCP configs |
| `config/packaging` | Packaging configs |
| `config/process.sdn` | Process config |
| `config/README_DOCKER.md` | Docker readme |
| `config/resources` | Resource files |
| `config/sdoctest.sdn` | Doc test config |
| `config/simple.intensive.sdn` | Intensive test config |
| `config/simple.test.sdn` | Test config |
| `config/t32` | TRACE32 configs |
| `config/t32_stm_linux_hidden.t32` | TRACE32 STM config |
| `config/themes` | Theme definitions |
| `config/traceability.sdn` | Traceability config |
| `config/FILE.md` | Config manifest |

## scripts/

| Entry | Description |
|---|---|
| `scripts/audit` | Audit scripts |
| `scripts/bootstrap` | Bootstrap scripts |
| `scripts/check` | Verification and evidence check scripts |
| `scripts/deps` | Dependency fetching scripts |
| `scripts/fpga` | FPGA board scripts (kria, jtag, flash) |
| `scripts/gui` | macOS GUI launcher scripts |
| `scripts/hooks` | Git hook scripts |
| `scripts/openocd` | OpenOCD configs |
| `scripts/os` | SimpleOS run and build scripts |
| `scripts/perf` | Performance scripts |
| `scripts/qemu` | QEMU test and setup scripts |
| `scripts/resource` | Resource files |
| `scripts/rtl` | RTL/FPGA generation scripts |
| `scripts/setup` | Project setup and install scripts |
| `scripts/smoke` | Protocol smoke test scripts |
| `scripts/check-workspace-root-guard.shs` | Workspace root guard |
| `scripts/FILE.md` | Scripts manifest |

## test/

| Entry | Description |
|---|---|
| `test/00_formal_verification` | Formal verification (Lean proofs) |
| `test/01_unit` | Unit tests |
| `test/02_integration` | Integration tests |
| `test/03_system` | System tests (includes feature tests) |
| `test/04_smoke` | Smoke tests |
| `test/05_perf` | Performance tests |
| `test/06_fuzz` | Fuzz tests |
| `test/07_security` | Security tests |
| `test/08_web_platform` | Web platform conformance tests |
| `test/09_baselines` | Baseline snapshots |
| `test/ci` | CI test configs |
| `test/fixtures` | Test fixtures |
| `test/shared` | Shared test utilities |
| `test/README.md` | Test readme |
| `test/FILE.md` | Test manifest |

## bin/

| Entry | Description |
|---|---|
| `bin/bb` | Bug tool |
| `bin/bug` | Bug report tool |
| `bin/jira` | Jira CLI |
| `bin/mail` | Email CLI |
| `bin/release` | Release directory |
| `bin/simple` | Main compiler binary |
| `bin/simple.bootstrap_seed_wrapper.c` | Bootstrap seed wrapper |
| `bin/simple.cmd` | Windows wrapper |
| `bin/simple.exe` | Windows executable |
| `bin/simple.freebsd` | FreeBSD binary |
| `bin/simple-interp` | Interpreter binary |
| `bin/simple_lsp_mcp_server.cmd` | LSP MCP server |
| `bin/simple_mcp_server.cmd` | MCP server |
| `bin/sj` | Simple jj wrapper |
| `bin/sj.cmd` | Windows sj wrapper |
| `bin/socat` | Socat wrapper |
| `bin/t32_lsp_mcp_server.cmd` | T32 LSP MCP |
| `bin/t32_mcp_server.cmd` | T32 MCP |
| `bin/codex_chrome_devtools_mcp.cmd` | Codex Chrome DevTools MCP |
| `bin/codex_stitch_mcp.cmd` | Codex Stitch MCP |
| `bin/FILE.md` | Bin manifest |
