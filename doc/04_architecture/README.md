# Architecture (Index)

## Core Documentation

- [Architecture Overview](overview.md) - High-level architecture and module dependencies
- [File & Class Structure](file_class_structure.md) - Comprehensive codebase inventory (5,644 files, 1.1M lines)
- [MDSOC Architecture](mdsoc_architecture_tobe.md) - Layered MDSOC view, shared tree nodes, layer violation fixes
- [MDSOC+ (ECS Business Layer)](mdsoc_architecture_tobe.md#mdsoc-plus-ecs-business-layer) - Default for userland services/apps: MDSOC outer + ECS inner
- [Architecture Details](architecture.md) - Overview, Structure, Dependencies
- [Module Details](architecture_modules.md) - Module Details, Type/Struct Listing
- [Data Flows](architecture_flows.md) - Data Flow, Execution, Memory Management
- [Development Guide](architecture_dev.md) - Feature Guidance, Code Quality, Verification
- [Glossary](glossary.md) - Key concepts (Crate, Virtual Crate, module terms)
- [Dependency Graphs](dependency_graphs.md) - Crate and module dependency graphs

## MDSOC Reports

- [Migration Status](../09_report/compiler_mdsoc_migration.md) - Implementation status, one-struct-per-file, symlink workarounds
- [Design](../01_research/compiler_mdsoc_design.md) - MDSoC + Clean Architecture applied to compiler pipeline
- [Feature Status](../02_requirements/feature/mdsoc_complete.md) - Current feature completion (288/288 tests)

## Additional Resources

See individual files in this directory for specialized topics (LLVM backend, memory model, etc.).

Relevant current feature slices:

- [KAIROS-Like Simple MCP + LLM Dashboard](kairos_like_simple_mcp_llm_dashboard.md) - Assistant/dashboard architecture, live bridge, and web-login/PBP bootstrap notes
