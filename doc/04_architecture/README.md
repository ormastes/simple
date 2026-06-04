# Architecture (Index)

## Folder Organization

`doc/04_architecture/` is the source of truth for architecture decisions,
system structure, runtime boundaries, and long-lived technical direction.

| Location | Use |
|----------|-----|
| `README.md` | Human entrypoint and folder policy |
| `*_tldr.md` | One-screen companion summaries for long architecture docs |
| `<feature>.md` | Feature, platform, runtime, or subsystem architecture |
| `adr/ADR-NNN-*.md` | Architecture Decision Records |
| `format/*.md` | File-format and wire-format architecture |
| `rule/*.md` | Architecture-adjacent engineering rules |

Keep existing architecture files in place unless a user explicitly asks for a
move. New architecture docs should use stable lowercase slugs, match the related
research/requirements/design/test slug when one exists, and link to source,
tests, reports, or generated specs with concrete paths.

## TLDR Companion Policy

Long architecture documents should have a same-directory TLDR file with the
same base name plus `_tldr.md`.

Examples:

| Original | TLDR |
|----------|------|
| `simpleos_launch_modes.md` | `simpleos_launch_modes_tldr.md` |
| `README.md` | `README_tldr.md` |
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

- [Architecture Overview](overview.md) - High-level architecture and module dependencies
- [File & Class Structure](file_class_structure.md) - Comprehensive codebase inventory (5,644 files, 1.1M lines)
- [MDSOC Architecture](mdsoc_architecture_tobe.md) - Layered MDSOC view, shared tree nodes, layer violation fixes
- [MDSOC+ (ECS Business Layer)](mdsoc_architecture_tobe.md#mdsoc-plus-ecs-business-layer) - Default for userland services/apps: MDSOC outer + ECS inner
- [Architecture Details](architecture.md) - Overview, Structure, Dependencies
- [Module Details](architecture_modules.md) - Module Details, Type/Struct Listing
- [Data Flows](architecture_flows.md) - Data Flow, Execution, Memory Management
- [Development Guide](architecture_dev.md) - Feature Guidance, Code Quality, Verification
- [Glossary](../glossary.md) - Key concepts (Crate, Virtual Crate, module terms)
- [Dependency Graphs](dependency_graphs.md) - Crate and module dependency graphs
- [Architecture Folder TLDR](README_tldr.md) - One-screen organization and TLDR policy
- [Simple App Startup](simple_app_startup.md) - Metadata-driven native/script/SMF/SimpleOS startup, mmap/cache, dynlib, and arg parser policy
- [Simple App Startup TLDR](simple_app_startup_tldr.md) - One-screen startup architecture summary

## MDSOC Reports

- [Migration Status](../09_report/compiler_mdsoc_migration.md) - Implementation status, one-struct-per-file, symlink workarounds
- [Design](../01_research/compiler_mdsoc_design.md) - MDSoC + Clean Architecture applied to compiler pipeline
- [Feature Status](../02_requirements/feature/mdsoc_complete.md) - Current feature completion (288/288 tests)

## Additional Resources

See individual files in this directory for specialized topics (LLVM backend, memory model, etc.).

Relevant current feature slices:

- [KAIROS-Like Simple MCP + LLM Dashboard](kairos_like_simple_mcp_llm_dashboard.md) - Assistant/dashboard architecture, live bridge, and web-login/PBP bootstrap notes
- [Graphics 3D Session Managed Backend](graphics_3d_session_managed_backend.md) - Common session architecture for 2D, 2D game, 3D, 3D game, web renderer, GUI, WM, and CPU/CUDA/Vulkan/Metal/WebGPU backends
