# Architecture (Index)

## Folder Organization

`doc/04_architecture/` is the source of truth for architecture decisions,
system structure, runtime boundaries, and long-lived technical direction.

| Location | Use |
|----------|-----|
| `README.md` | Human entrypoint and folder policy |
| `adr/ADR-NNN-*.md` | Architecture Decision Records |
| `app/` | Application-facing architecture for compiler tools, MCP/LSP, SPipe, UI apps, and repo tools |
| `compiler/` | Compiler, backend, optimization, SIMD, graphics-backend, and MDSOC architecture |
| `format/*.md` | File-format and wire-format architecture |
| `hardware/` | Hardware, RISC-V, VHDL, TRACE32, and bare-metal integration architecture |
| `infra/` | Documentation-system, security, workspace, and cross-cutting infrastructure architecture |
| `language/` | Language/module/package semantics and feature-module architecture |
| `lib/` | Standard library and reusable runtime-library architecture |
| `ml/` | ML and accelerator planning architecture |
| `os/` | OS, SimpleOS, scheduler, driver, and storage architecture |
| `platform/` | Host/platform interop architecture |
| `rule/*.md` | Architecture-adjacent engineering rules |
| `runtime/` | JIT/interpreter, native-runtime, runtime-family, and concurrency architecture |
| `startup/` | Launch metadata, argv, mmap/read-ahead, dynlib, and SimpleOS startup architecture |
| `test/` | Test runner, SPipe, markdown/Sdoctest, remote, QEMU, and bare-metal test architecture |
| `ui/` | UI, GUI, web-renderer, graphics, and UI-test architecture |

Root-level architecture docs are intentionally limited to this index. New
architecture docs should live under the narrowest matching topic folder, use
stable lowercase slugs, match the related research/requirements/design/test slug
when one exists, and link to source, tests, reports, or generated specs with
concrete paths.

## TLDR Companion Policy

Long architecture documents should have a same-directory TLDR file with the
same base name plus `_tldr.md`.

Examples:

| Original | TLDR |
|----------|------|
| `os/simpleos/kernel/simpleos_launch_modes.md` | `os/simpleos/kernel/simpleos_launch_modes_tldr.md` |
| `infra/architecture_docs/overview/README.md` | `infra/architecture_docs/overview/README_tldr.md` |
| `format/smf_specification.md` | `format/smf_specification_tldr.md` |

Do not create `*_tldr_tldr.md`. Do not put executable SPipe specs under
`doc/06_spec`; generated/manual spec docs stay there, while architecture TLDRs
stay beside their architecture source document.

TLDR files should fit on one screen and answer:

- what the architecture doc is for
- the core decision or structure
- startup, hot-path, cache/index, invalidation, and RSS/latency implications
  when relevant
- the few paths a maintainer should open next

## Core Documentation

- [Architecture Overview](infra/architecture_docs/overview/overview.md) - High-level architecture and module dependencies
- [Architecture Details](infra/architecture_docs/overview/architecture.md) - Overview, structure, dependencies
- [File & Class Structure](compiler/misc/file_class_structure.md) - Codebase inventory
- [MDSOC Architecture](compiler/mdsoc/mdsoc_architecture_tobe.md) - Layered MDSOC view, shared tree nodes, layer violation fixes
- [MDSOC+ (ECS Business Layer)](compiler/mdsoc/mdsoc_architecture_tobe.md#mdsoc-plus-ecs-business-layer) - Default for userland services/apps: MDSOC outer + ECS inner
- [Module Details](language/architecture_modules.md) - Module details and type/struct listing
- [Data Flows](infra/architecture_docs/flows/architecture_flows.md) - Data flow, execution, memory management
- [Development Guide](infra/architecture_docs/dev_docs/architecture_dev.md) - Feature guidance, code quality, verification
- [Glossary](../glossary.md) - Key concepts (Crate, Virtual Crate, module terms)
- [Dependency Graphs](infra/misc/dependency_graphs.md) - Crate and module dependency graphs
- [Architecture Folder TLDR](infra/architecture_docs/overview/README_tldr.md) - One-screen organization and TLDR policy
- [Compiler Architecture](compiler/00_compiler_architecture.md) - Compiler pipeline, layers, backend contracts, and metadata handoff
- [Startup Architecture](startup/00_startup_architecture.md) - Metadata-driven native/script/SMF/SimpleOS startup, mmap/cache, dynlib, and arg parser policy
- [UI Architecture](ui/00_ui_architecture.md) - Semantic UI state, render/Draw IR, shell adapters, and UI test location model
- [Web Framework Architecture](ui/web/00_web_framework_architecture.md) - Web framework flow connected to UI snapshots and `ui.web`
- [Test Architecture](test/00_test_architecture.md) - Test runner, SPipe, markdown/Sdoctest, remote, QEMU, and bare-metal lanes

## MDSOC Reports

- [Migration Status](../09_report/compiler_mdsoc_migration.md) - Implementation status, one-struct-per-file, symlink workarounds
- [Design](../01_research/compiler_mdsoc_design.md) - MDSoC + Clean Architecture applied to compiler pipeline
- [Feature Status](../02_requirements/feature/mdsoc_complete.md) - Current feature completion (288/288 tests)

## Additional Resources

See individual files in this directory for specialized topics (LLVM backend, memory model, etc.).

Relevant current feature slices:

- [Low Dependency UI dynSMF](ui/low_dependency_ui_dynsmf.md) - UI dependency boundaries and session-owned dynSMF runtime
- [Multicore Green](runtime/multicore_green.md) - Runtime-pool M:N candidate and SimpleOS green-carrier architecture
- [Simple Feature Module](language/simple_feature_module.md) - `.sfm` container and manifest capsule architecture
- [Simple 3D Graph IR](ui/graphics/simple_3d_graph_ir.md) - Backend-neutral 3D draw scheduling architecture
- [SimpleOS NVFS Submodule Migration](os/storage/simpleos_nvfs_submodule_migration.md) - OS-owned NVFS service package migration
- [KAIROS-Like Simple MCP + LLM Dashboard](app/ui/kairos_like_simple_mcp_llm_dashboard.md) - Assistant/dashboard architecture, live bridge, and web-login/PBP bootstrap notes
- [Graphics 3D Session Managed Backend](compiler/graphics/graphics_3d_session_managed_backend.md) - Common session architecture for 2D, 2D game, 3D, 3D game, web renderer, GUI, WM, and CPU/CUDA/Vulkan/Metal/WebGPU backends
