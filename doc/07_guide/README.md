# Simple Language Guides

User-facing guides for the Simple programming language. For specifications see `doc/06_spec/`, for research see `doc/01_research/`.

---

## Getting Started

| Guide | Description |
|-------|-------------|
| [getting_started.md](getting_started.md) | Installation, first program, language basics |
| [build.md](build.md) | Build system, SDN config, bootstrap |
| [cli.md](cli.md) | CLI commands, arguments, stats |

## Language

| Guide | Description |
|-------|-------------|
| [language/syntax.md](language/syntax.md) | Core syntax, constructors, lambdas, collections, blocks |
| [language/type_system.md](language/type_system.md) | Types, advanced types, newtypes, type checking |
| [language/module_system.md](language/module_system.md) | Imports, exports, `__init__.spl` |
| [language/error_handling.md](language/error_handling.md) | `Result<T,E>`, `?` operator, error recovery |
| [language/coding_style.md](language/coding_style.md) | Style guide, common mistakes |

## Testing

| Guide | Description |
|-------|-------------|
| [testing/testing.md](testing/testing.md) | SSpec framework, matchers, mocking, helpers |
| [testing/coverage.md](testing/coverage.md) | Source coverage, doc coverage |
| [testing/container_testing.md](testing/container_testing.md) | Container-based isolated testing |
| [testing/benchmarking.md](testing/benchmarking.md) | Performance benchmarking |

## Tooling

| Guide | Description |
|-------|-------------|
| [tooling/repl.md](tooling/repl.md) | Interactive REPL — commands, multi-line, state |
| [tooling/jupyter.md](tooling/jupyter.md) | Jupyter kernel — notebooks, installation, testing |
| [tooling/lsp_dap.md](tooling/lsp_dap.md) | LSP + DAP setup (VSCode, Neovim) |
| [tooling/mcp.md](tooling/mcp.md) | MCP server setup and usage |
| [tooling/ui_access.md](tooling/ui_access.md) | Canonical UI snapshot, act, and history workflow |
| [tooling/treesitter.md](tooling/treesitter.md) | Tree-sitter integration |
| [tooling/dashboard.md](tooling/dashboard.md) | Dashboard CLI, CI/CD |
| [tooling/duplicate_check.md](tooling/duplicate_check.md) | Code duplication detection |
| [tooling/wm_compare.md](tooling/wm_compare.md) | WM screenshot capture and compare harness |
| [tooling/wm_ui_snapshot.md](tooling/wm_ui_snapshot.md) | WM/UI HTML snapshot export, PNG generation, Stitch handoff |
| [tooling/script_layout_policy.md](tooling/script_layout_policy.md) | `scripts/` vs `bin/` policy, `.shs` rule, ignore list |

## FFI

| Guide | Description |
|-------|-------------|
| [ffi/sffi.md](ffi/sffi.md) | SFFI patterns, gen guide, syscalls |
| [ffi/wrapper_gen.md](ffi/wrapper_gen.md) | C++/Rust wrapper generation |

## Tools

| Guide | Description |
|-------|-------------|
| [tools/t32_cli.md](tools/t32_cli.md) | T32 CLI — TRACE32 GUI-to-CLI converter, interactive shell |
| [tools/mcp_t32.md](tools/mcp_t32.md) | T32 MCP Server — 20-tool MCP for TRACE32 debug sessions |

## Backend

| Guide | Description |
|-------|-------------|
| [backend/backends.md](backend/backends.md) | Backend selection, capabilities, shared components |
| [backend/gpu_programming.md](backend/gpu_programming.md) | GPU (CUDA + Vulkan), SIMD, config |
| [backend/baremetal.md](backend/baremetal.md) | Baremetal, QEMU, semihosting, embedded |

## Deep Learning

| Guide | Description |
|-------|-------------|
| [deep_learning/deep_learning.md](deep_learning/deep_learning.md) | DL guide, pure Simple DL, PyTorch integration |
| [deep_learning/tensor_dimensions.md](deep_learning/tensor_dimensions.md) | Dimension inference, errors, transforms |

## Platform

| Guide | Description |
|-------|-------------|
| [platform/platforms.md](platform/platforms.md) | Platform support, FreeBSD, cross-compilation |
| [platform/packaging.md](platform/packaging.md) | Packages, deployment, GitHub |
| [platform/simpleos_dev_guide.md](platform/simpleos_dev_guide.md) | SimpleOS tooling, bootstrap, native build and run workflow |
| [platform/simpleos_web_wm.md](platform/simpleos_web_wm.md) | Browser-hosted SimpleOS Web WM runtime |

## Architecture

| Guide | Description |
|-------|-------------|
| [architecture/application_architecture.md](architecture/application_architecture.md) | Standard architecture, MDSoC |
| [architecture/compiler_architecture.md](architecture/compiler_architecture.md) | Compiler pipeline overview |
| [architecture/async.md](architecture/async.md) | Async/await, generators, actors |

## Library

| Guide | Description |
|-------|-------------|
| [library/stdlib.md](library/stdlib.md) | SDN, strings, collections, DB, SQP |
| [library/security.md](library/security.md) | Security library, sanitization, capability policy, security AOP |
| [library/web_framework.md](library/web_framework.md) | Web framework, HTTP |
| [library/ui.md](library/ui.md) | UI framework (.sui files) |
| [library/library_smf.md](library/library_smf.md) | Library SMF creation and usage |

## Writing

| Guide | Description |
|-------|-------------|
| [writing/application_writing.md](writing/application_writing.md) | Application dev methodology |
| [writing/design_writing.md](writing/design_writing.md) | Design-first development |
| [writing/architecture_writing.md](writing/architecture_writing.md) | Architecture-first development |
| [writing/folder_file.md](writing/folder_file.md) | Project structure guide |

## Quick Reference

| Guide | Description |
|-------|-------------|
| [quick_reference/syntax_quick_reference.md](quick_reference/syntax_quick_reference.md) | Canonical public syntax reference |
| [quick_reference/import_quick_reference.md](quick_reference/import_quick_reference.md) | Import patterns |
| [quick_reference/dap_quick_reference.md](quick_reference/dap_quick_reference.md) | DAP commands |
| [quick_reference/test_helpers_quick_reference.md](quick_reference/test_helpers_quick_reference.md) | Test helpers |

## Source Of Truth

- Hand-written guides in `07_guide/` describe the canonical public language surface.
- Generated grammar/status docs live under [`../06_spec/app/compiler/modules/grammar/`](../06_spec/app/compiler/modules/grammar/).
- Generated feature docs under `02_requirements/feature/` may include deprecated or compatibility syntax when the test itself is about parser recovery or migration.
