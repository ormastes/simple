# The Simple Language Manual

Welcome to the official manual for the **Simple** programming language -- a self-hosted, systems-capable language with a clean syntax, algebraic type system, and multi-backend compiler. Whether you are writing your first program or building GPU kernels, this manual covers everything you need.

For language specifications see `doc/spec/`. For research notes see `doc/research/`.

---

## Part I: Getting Started

| # | Chapter | Description |
|---|---------|-------------|
| 1 | [Getting Started](getting_started.md) | Installation, your first program, and language basics |
| 2 | [CLI Reference](cli.md) | Command-line interface, arguments, subcommands, and stats |
| 3 | [Build System](build.md) | Build modes, SDN configuration, bootstrap process, and release builds |

## Part II: The Language

| # | Chapter | Description |
|---|---------|-------------|
| 4 | [Syntax](language/syntax.md) | Core syntax, constructors, lambdas, collections, comprehensions, and blocks |
| 5 | [Type System](language/type_system.md) | Primitive types, generics, traits, newtypes, algebraic types, and type inference |
| 6 | [Error Handling](language/error_handling.md) | `Result<T, E>`, the `?` operator, error propagation, and recovery patterns |
| 7 | [Module System](language/module_system.md) | Imports, exports, `__init__.spl`, visibility rules, and package resolution |
| 8 | [Coding Style](language/coding_style.md) | Style conventions, naming, formatting, and common mistakes to avoid |

## Part III: Standard Library

| # | Chapter | Description |
|---|---------|-------------|
| 9 | [Standard Library Overview](library/stdlib.md) | SDN, strings, collections, database, SQP, and core APIs |
| 10 | [Library Packaging (SMF)](library/library_smf.md) | Creating and consuming Simple Module Format libraries |
| 11 | [UI Framework](library/ui.md) | Declarative UI with `.sui` files, components, and layout |
| 12 | [Web Framework](library/web_framework.md) | HTTP server, routing, middleware, and request handling |

## Part IV: Testing

| # | Chapter | Description |
|---|---------|-------------|
| 13 | [Testing with SSpec](testing/testing.md) | BDD framework, matchers, mocking, test helpers, and test organization |
| 14 | [Benchmarking](testing/benchmarking.md) | Performance measurement, benchmark suites, and result analysis |
| 15 | [Container Testing](testing/container_testing.md) | Isolated test execution in containers for reproducible CI |
| 16 | [Coverage](testing/coverage.md) | Source code coverage, documentation coverage, and coverage reporting |

## Part V: Tooling

| # | Chapter | Description |
|---|---------|-------------|
| 17 | [Linter](tooling/lint.md) | Built-in lint rules, configuration, and auto-fix |
| 18 | [LSP and DAP](tooling/lsp_dap.md) | Language Server Protocol and Debug Adapter Protocol setup for VSCode and Neovim |
| 19 | [REPL](tooling/repl.md) | Interactive read-eval-print loop, multi-line input, and session state |
| 20 | [Jupyter Integration](tooling/jupyter.md) | Jupyter kernel installation, notebook usage, and testing |
| 21 | [MCP Server](tooling/mcp.md) | Model Context Protocol server setup and tool definitions |
| 22 | [Tree-sitter](tooling/treesitter.md) | Tree-sitter grammar, syntax highlighting, and editor integration |
| 23 | [Dashboard](tooling/dashboard.md) | Project dashboard CLI and CI/CD integration |
| 24 | [Duplication Detection](tooling/duplicate_check.md) | Code duplication analysis and refactoring guidance |
| 25 | [SHB Binary Format](tooling/shb.md) | Module interface caching, SHB generation, and consumers |
| 26 | [TRACE32 CLI](tools/t32_cli.md) | TRACE32 GUI-to-CLI converter and interactive debug shell |
| 27 | [TRACE32 MCP Server](tools/mcp_t32.md) | 20-tool MCP server for TRACE32 debug sessions |

## Part VI: Advanced Topics

### Compiler Backends

| # | Chapter | Description |
|---|---------|-------------|
| 28 | [Backend Overview](backend/backends.md) | Backend selection, capabilities matrix, and shared compiler components |
| 29 | [Baremetal and Embedded](backend/baremetal.md) | Baremetal targets, QEMU, semihosting, and embedded development |
| 30 | [GPU Programming](backend/gpu_programming.md) | CUDA and Vulkan backends, SIMD intrinsics, and GPU kernel syntax |
| 31 | [TRACE32 Docker Setup](backend/trace32_docker_experiment.md) | Running TRACE32 in Docker for automated hardware debugging |
| 32 | [TRACE32 Linux Setup](backend/trace32_linux_setup.md) | Native TRACE32 installation and configuration on Linux |

### Foreign Function Interface

| # | Chapter | Description |
|---|---------|-------------|
| 33 | [SFFI Guide](ffi/sffi.md) | Simple FFI patterns, code generation, and syscall wrappers |
| 34 | [Wrapper Generation](ffi/wrapper_gen.md) | Automated C++ and Rust wrapper generation from headers |

### Deep Learning

| # | Chapter | Description |
|---|---------|-------------|
| 35 | [Deep Learning](deep_learning/deep_learning.md) | Pure Simple neural networks, PyTorch interop, and ML pipeline operators |
| 36 | [Tensor Dimensions](deep_learning/tensor_dimensions.md) | Compile-time dimension inference, shape errors, and tensor transforms |

### Compiler Architecture

| # | Chapter | Description |
|---|---------|-------------|
| 37 | [Compiler Pipeline](architecture/compiler_architecture.md) | Compiler phases, IR layers, optimization passes, and code generation |
| 38 | [Application Architecture](architecture/application_architecture.md) | Standard application structure and MDSoC patterns |
| 39 | [Async Programming](architecture/async.md) | Async/await, generators, actors, and concurrency primitives |

### Platform Support

| # | Chapter | Description |
|---|---------|-------------|
| 40 | [Platforms](platform/platforms.md) | Supported platforms, FreeBSD, cross-compilation, and platform-specific notes |
| 41 | [Packaging and Distribution](platform/packaging.md) | Package creation, deployment pipelines, and GitHub releases |

## Part VII: Development Methodology

| # | Chapter | Description |
|---|---------|-------------|
| 42 | [Application Development](writing/application_writing.md) | End-to-end application development methodology |
| 43 | [Design-First Development](writing/design_writing.md) | Design document workflow and design-driven implementation |
| 44 | [Architecture-First Development](writing/architecture_writing.md) | Architecture planning before coding |
| 45 | [Project Structure](writing/folder_file.md) | Recommended folder layout and file organization |

## Additional References

| # | Reference | Description |
|---|-----------|-------------|
| 46 | [CMM Language Reference](cmm_language_reference.md) | TRACE32 CMM/PRACTICE scripting language reference |
| 47 | [FreeBSD QEMU Testing](freebsd_qemu_testing.md) | FreeBSD test environment setup with QEMU |

---

## Appendices: Quick Reference Cards

| Appendix | Reference | Description |
|----------|-----------|-------------|
| A | [Syntax Quick Reference](quick_reference/syntax_quick_reference.md) | Complete syntax cheat sheet -- operators, keywords, patterns |
| B | [Import Quick Reference](quick_reference/import_quick_reference.md) | Import statement patterns and module resolution rules |
| C | [DAP Quick Reference](quick_reference/dap_quick_reference.md) | Debug Adapter Protocol commands and configuration |
| D | [Test Helpers Quick Reference](quick_reference/test_helpers_quick_reference.md) | SSpec matchers, hooks, and test utility functions |
