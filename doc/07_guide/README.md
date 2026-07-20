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
| [language/units.md](language/units.md) | Unit system -- directory layout, postfix literals, imports, composite units, raw-primitive warning |

## Testing

| Guide | Description |
|-------|-------------|
| [testing/testing.md](testing/testing.md) | SPipe framework, matchers, mocking, helpers |
| [testing/coverage.md](testing/coverage.md) | Source coverage, doc coverage |
| [testing/container_testing.md](testing/container_testing.md) | Container-based isolated testing |
| [testing/benchmarking.md](testing/benchmarking.md) | Performance benchmarking |
| [testing/test_layout_traceability.md](testing/test_layout_traceability.md) | Canonical test roots, mirrored SPipe docs, and move checklist |
| [testing/mock_policy_system_test_ban.md](testing/mock_policy_system_test_ban.md) | Mock policy and system test ban rules |
| [testing/tauri_backend_container_testing.md](testing/tauri_backend_container_testing.md) | Tauri backend container testing |

## Tooling

| Guide | Description |
|-------|-------------|
| [tooling/repl.md](tooling/repl.md) | Interactive REPL -- commands, multi-line, state |
| [tooling/jupyter.md](tooling/jupyter.md) | Jupyter kernel -- notebooks, installation, testing |
| [tooling/lsp_dap.md](tooling/lsp_dap.md) | LSP + DAP setup (VSCode, Neovim) |
| [tooling/mcp.md](tooling/mcp.md) | MCP server setup and usage |
| [tooling/lint.md](tooling/lint.md) | Linter configuration and usage |
| [tooling/logging.md](tooling/logging.md) | Production logging, debug logging, and script print policy |
| [infra/debugging/easy_debug_infra.md](infra/debugging/easy_debug_infra.md) | `std.diag` debug primitives -- stage tracer, cooperative watchdog, aggregating timers/counters, event-chain tracer, provenance assert |
| [app/ui/ui_access.md](app/ui/ui_access.md) | Canonical UI snapshot, act, and history workflow |
| [app/ui/engine2d_backend_order.md](app/ui/engine2d_backend_order.md) | Engine2D GUI backend preference order and font offload lanes |
| [app/ui/ui_render.md](app/ui/ui_render.md) | UI rendering pipeline, shared web render contract, HTML/CSS cache planning |
| [tooling/llm_dashboard_web_login.md](tooling/llm_dashboard_web_login.md) | Web login, bootstrap admin credentials, and auth-session storage for `llm_dashboard` |
| [tooling/llm_approval_flow.md](tooling/llm_approval_flow.md) | LLM approval flow |
| [tooling/treesitter.md](tooling/treesitter.md) | Tree-sitter integration |
| [tooling/dashboard.md](tooling/dashboard.md) | Dashboard CLI, CI/CD |
| [tooling/duplicate_check.md](tooling/duplicate_check.md) | Code duplication detection |
| [app/ui/wm_compare.md](app/ui/wm_compare.md) | WM screenshot capture and compare harness |
| [app/ui/wm_ui_snapshot.md](app/ui/wm_ui_snapshot.md) | WM/UI HTML snapshot export, PNG generation, Stitch handoff |
| [app/devhub.md](app/devhub.md) | devhub CLI -- gh/mc/Gmail-shaped UX over Jira, GitHub, Bitbucket, Confluence, MinIO/S3, and email backends |
| [tooling/script_layout_policy.md](tooling/script_layout_policy.md) | `scripts/` vs `bin/` policy, `.shs` rule, ignore list |
| [tooling/ai_cli_registration.md](tooling/ai_cli_registration.md) | AI CLI plugin registration |
| [tooling/ai_command_parity.md](tooling/ai_command_parity.md) | AI command parity across providers |
| [tooling/ai_plugin_status.md](tooling/ai_plugin_status.md) | AI plugin status dashboard |

## API

| Guide | Description |
|-------|-------------|
| [api/gpu_api.md](api/gpu_api.md) | GPU API reference |
| [api/note_sdn_api.md](api/note_sdn_api.md) | SDN API notes |
| [api/sdn_graph.md](api/sdn_graph.md) | SDN graph syntax, CSS labels, weaving, and Markdown embedding |
| [api/markdown_document_decoration.md](api/markdown_document_decoration.md) | Markdown CSS, page view, header, and footer document rendering |
| [api/pure_dl_api_reference.md](api/pure_dl_api_reference.md) | Pure DL API reference |
| [api/webgpu_guide.md](api/webgpu_guide.md) | WebGPU usage guide |

## Library

| Guide | Description |
|-------|-------------|
| [lib/misc/stdlib.md](lib/misc/stdlib.md) | Standard library guide, including SDN, text utilities, concurrency primitives, and database access |

## FFI

| Guide | Description |
|-------|-------------|
| [ffi/sffi.md](ffi/sffi.md) | SFFI patterns, gen guide, syscalls |
| [ffi/wrapper_gen.md](ffi/wrapper_gen.md) | C++/Rust wrapper generation |
| [ffi/external_native_libraries.md](ffi/external_native_libraries.md) | External native library integration |

## Tools

| Guide | Description |
|-------|-------------|
| [tools/t32_cli.md](tools/t32_cli.md) | T32 CLI -- TRACE32 GUI-to-CLI converter, interactive shell |
| [tools/mcp_t32.md](tools/mcp_t32.md) | T32 MCP Server -- 20-tool MCP for TRACE32 debug sessions |
| [tools/simpleos_shell_scripting.md](tools/simpleos_shell_scripting.md) | SimpleOS shell scripting |
| [tools/terminal_power_setup.md](tools/terminal_power_setup.md) | Terminal power setup and configuration |

## Backend

| Guide | Description |
|-------|-------------|
| [compiler/backends/backends.md](compiler/backends/backends.md) | Backend selection, capabilities, shared components |
| [compiler/backends/gpu_programming.md](compiler/backends/gpu_programming.md) | GPU (CUDA + Vulkan), SIMD, config |
| [compiler/backends/processing_backend.md](compiler/backends/processing_backend.md) | Portable ProcessingIR path for CPU, Vulkan, CUDA, RV64GCV, VHDL/RTL, and simplegpu64 |
| [compiler/backends/baremetal.md](compiler/backends/baremetal.md) | Baremetal, QEMU, semihosting, embedded |
| [compiler/llvm/llvm_backend_policy.md](compiler/llvm/llvm_backend_policy.md) | LLVM backend policy |
| [compiler/llvm/llvm_optimization_workflow.md](compiler/llvm/llvm_optimization_workflow.md) | LLVM optimization workflow, IR quality, verification, benchmark gate |
| [backend/trace32_docker_experiment.md](backend/trace32_docker_experiment.md) | TRACE32 Docker experiment |
| [backend/trace32_linux_setup.md](backend/trace32_linux_setup.md) | TRACE32 Linux setup |

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
| [platform/simpleos/simpleos_dev_guide.md](platform/simpleos/simpleos_dev_guide.md) | SimpleOS tooling, bootstrap, native build and run workflow |
| [platform/simpleos/simpleos_arm64_wm_qemu.md](platform/simpleos/simpleos_arm64_wm_qemu.md) | ARM64 SimpleOS WM QEMU ramfb verification |
| [platform/misc/sosix_process_scheduler.md](platform/misc/sosix_process_scheduler.md) | SOSIX process APIs, immutable sharing, scheduler classes, and current kernel limits |
| [platform/simpleos/simpleos_web_wm.md](platform/simpleos/simpleos_web_wm.md) | Browser-hosted SimpleOS Web WM runtime |

## Architecture

| Guide | Description |
|-------|-------------|
| [architecture/application_architecture.md](architecture/application_architecture.md) | Standard architecture, MDSoC |
| [architecture/compiler_architecture.md](architecture/compiler_architecture.md) | Compiler pipeline overview |
| [architecture/async.md](architecture/async.md) | Async/await, generators, actors |
| [architecture/module_resolver.md](architecture/module_resolver.md) | Module resolver internals |

## Contributing

| Guide | Description |
|-------|-------------|
| [contributing/i18n.md](contributing/i18n.md) | Internationalization guide |
| [contributing/i18n_translation.md](contributing/i18n_translation.md) | Translation workflow |

## Hardware

| Guide | Description |
|-------|-------------|
| [hardware/mlk_s02_100t_assumed_profile.md](hardware/mlk_s02_100t_assumed_profile.md) | MLK-S02 100T assumed profile |
| [hardware/mlk_s02_100t_vendor_download_guide.md](hardware/mlk_s02_100t_vendor_download_guide.md) | MLK-S02 100T vendor download guide |
| [hardware/simple_generated_fpga_rtl.md](hardware/simple_generated_fpga_rtl.md) | Simple-generated FPGA RTL |
| [hardware/xilinx_fpga_board_bringup.md](hardware/xilinx_fpga_board_bringup.md) | Xilinx FPGA board bringup |

## Storage / Filesystem

| Guide | Description |
|-------|-------------|
| [fs_driver.md](fs_driver.md) | How to add a filesystem driver, consume `FsDriver`, and extend the FAT32/NVFS system-test matrix |

## Library

| Guide | Description |
|-------|-------------|
| [library/stdlib.md](library/stdlib.md) | SDN, strings, collections, DB, SQP |
| [library/security.md](library/security.md) | Security library, sanitization, capability policy, security AOP |
| [library/web_framework.md](library/web_framework.md) | Web framework, HTTP |
| [library/ui.md](library/ui.md) | UI framework (.sui files) |
| [library/library_smf.md](library/library_smf.md) | Library SMF creation and usage |
| [library/engine3d.md](library/engine3d.md) | 3D engine library |
| [lib/shared_multilingual_gpu_fonts.md](lib/shared_multilingual_gpu_fonts.md) | Pinned multilingual fonts, shared rendering, and GPU emission |

## Theme

| Guide | Description |
|-------|-------------|
| [theme/stitch_simple_os_theme.md](theme/stitch_simple_os_theme.md) | Stitch SimpleOS theme integration |

## SimpleOS

| Guide | Description |
|-------|-------------|
| [simpleos_apps.md](simpleos_apps.md) | SimpleOS desktop applications guide -- all 30 apps, widget builder DSL, entry points |
| [simpleos_driver_platform_index.md](simpleos_driver_platform_index.md) | SimpleOS driver/platform plan and test routing index |
| [simpleos_executable_format.md](simpleos_executable_format.md) | SimpleOS executable format |
| [userspace_spawn_api.md](userspace_spawn_api.md) | Userspace spawn API |
| [ui_stack_guide.md](ui_stack_guide.md) | UI stack guide |

## Compiler

| Guide | Description |
|-------|-------------|
| [compiler_optimization_levels.md](compiler_optimization_levels.md) | Compiler optimization levels |
| [compiler_optimization_plugin.md](compiler_optimization_plugin.md) | Simple Optimization Plugin guide -- reusable optimizer providers, built-in vs dynamic load modes, safety and validation |
| [compiler_simd_auto_application.md](compiler_simd_auto_application.md) | SIMD auto-application maintainer guide -- rewrite rules, fallback, duplication checks, tests |

## Miscellaneous

| Guide | Description |
|-------|-------------|
| [browser_engine_implementation.md](browser_engine_implementation.md) | Browser engine implementation guide |
| [cmm_language_reference.md](cmm_language_reference.md) | CMM language reference |
| [driver_authoring.md](driver_authoring.md) | Driver authoring guide |
| [dynlib_api.md](dynlib_api.md) | Dynamic library API |
| [execve_syscall.md](execve_syscall.md) | Execve syscall guide |
| [lean_verification_workflow.md](lean_verification_workflow.md) | Lean verification workflow |
| [tooling/pure_simple_tooling.md](tooling/pure_simple_tooling.md) | Pure Simple tool dispatch, test-daemon, and completion gate |
| [ssh_serial_transport.md](ssh_serial_transport.md) | SSH serial transport |
| [wine_dll_loading.md](wine_dll_loading.md) | Wine DLL loading |

## Writing

| Guide | Description |
|-------|-------------|
| [writing/application_writing.md](writing/application_writing.md) | Application dev methodology |
| [writing/design_writing.md](writing/design_writing.md) | Design-first development |
| [writing/architecture_writing.md](writing/architecture_writing.md) | Architecture-first development |
| [writing/folder_file.md](writing/folder_file.md) | Project structure guide |
| [writing/traceability.md](writing/traceability.md) | Traceability guide |

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
