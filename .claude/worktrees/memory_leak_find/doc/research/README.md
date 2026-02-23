# Research Documentation

**Purpose:** Design documents, technical research, and architecture explorations for Simple language features and implementation strategies.

**Status:** Active research and design documents
**Last Updated:** 2025-12-28

---

## Overview

This directory contains in-depth research documents exploring:
- Performance optimization strategies
- Architecture decisions and trade-offs
- Technology comparisons and benchmarks
- Integration strategies for external tools
- API design principles

**Note:** Research documents are exploratory. See [doc/spec/](../spec/) for stable specifications and [doc/status/](../status/) for implementation status.

---

## Categories

### Performance & Optimization (8 documents)

| Document | Topic | Status |
|----------|-------|--------|
| [high_performance_concurrent_runtime.md](high_performance_concurrent_runtime.md) | Multi-threading, work-stealing, async runtime | Design |
| [io_uring_vs_mmap_performance.md](io_uring_vs_mmap_performance.md) | I/O performance comparison | Analysis |
| [src_to_bin_optimization.md](src_to_bin_optimization.md) | Build optimization strategies | Design |
| [mold_linker_analysis.md](mold_linker_analysis.md) | Fast linker comparison | Analysis |
| [codegen_backend_comparison.md](codegen_backend_comparison.md) | Cranelift vs LLVM | Analysis |
| [codegen_body_outlining.md](codegen_body_outlining.md) | Generator/actor body optimization | Design |
| [async_mmap_file_api.md](async_mmap_file_api.md) | Async file I/O with memory mapping | Design |
| [interpreter_vs_codegen.md](interpreter_vs_codegen.md) | Hybrid execution strategy | Analysis |

### GPU & SIMD (4 documents)

| Document | Topic | Status |
|----------|-------|--------|
| [cpu_simd_scheduling.md](cpu_simd_scheduling.md) | TBB-style parallel scheduling for @simd | Design |
| [simd_to_tbb_transformation.md](simd_to_tbb_transformation.md) | @simd to Rayon/TBB lowering | Design |
| [cuda_tbb_entry_compare.md](cuda_tbb_entry_compare.md) | CUDA vs TBB programming models | Comparison |
| [gpu_compute_backends.md](gpu_compute_backends.md) | CUDA/Vulkan/Metal backend options | Analysis |

### 3D Graphics & Game Engines (4 documents)

| Document | Topic | Status |
|----------|-------|--------|
| [3D_GAME_ENGINE_INTEGRATION_RESEARCH.md](3D_GAME_ENGINE_INTEGRATION_RESEARCH.md) | Godot/Unreal integration research | Research |
| [game_engine_3d_integration.md](game_engine_3d_integration.md) | 3D engine architecture | Design |
| [game_engine_architecture.md](game_engine_architecture.md) | Entity-component-system design | Design |
| [game_engine_scene_graph.md](game_engine_scene_graph.md) | Scene hierarchy and transforms | Design |

### UI Frameworks (5 documents)

| Document | Topic | Status |
|----------|-------|--------|
| [async_ui_architecture.md](async_ui_architecture.md) | Async UI event handling | Design |
| [electron_vscode_testing_2025.md](electron_vscode_testing_2025.md) | VSCode extension architecture | Research |
| [REPL_BACKSPACE_LIMITATION.md](REPL_BACKSPACE_LIMITATION.md) | Terminal REPL input handling | Analysis |
| [BACKSPACE_FIX_RESEARCH.md](BACKSPACE_FIX_RESEARCH.md) | Crossterm/ratatui backspace fixes | Research |
| [TERMINAL_SEQUENCE_CAPTURE.md](TERMINAL_SEQUENCE_CAPTURE.md) | Raw terminal sequence capture | Research |

### API Design (4 documents + subdirectory)

| Document | Topic | Status |
|----------|-------|--------|
| [api_design_index.md](api_design_index.md) | Comprehensive API design guide | Reference |
| [improve_api.md](improve_api.md) | API design overview | Overview |
| [api_design_regrets.md](api_design_regrets.md) | Lessons learned from API mistakes | Retrospective |
| [immutable_interface_design.md](immutable_interface_design.md) | Immutable API patterns | Design |
| [api_design/](api_design/) | Detailed API design topics | Subdirectory |

### Runtime & Concurrency (5 documents)

| Document | Topic | Status |
|----------|-------|--------|
| [actor_runtime_policy.md](actor_runtime_policy.md) | Actor model runtime behavior | Design |
| [runtime_ffi_design.md](runtime_ffi_design.md) | FFI function design patterns | Design |
| [zero_copy_ffi.md](zero_copy_ffi.md) | Zero-copy FFI boundaries | Design |
| [memory_model_sc_drf.md](memory_model_sc_drf.md) | Sequential consistency memory model | Specification |
| [reference_capabilities_design.md](reference_capabilities_design.md) | Pony-style reference capabilities | Design |

### Language Features (9 documents)

| Document | Topic | Status |
|----------|-------|--------|
| [code_shortening_grammar_analysis.md](code_shortening_grammar_analysis.md) | High-leverage syntax features analysis | Analysis |
| [statement_container_grammars.md](statement_container_grammars.md) | Cross-language grammar comparison | Research |
| [aop.md](aop.md) | Aspect-oriented programming | Design |
| [dependency_injection.md](dependency_injection.md) | DI container design | Design |
| [metaprogramming_design.md](metaprogramming_design.md) | Macro system architecture | Design |
| [pattern_matching_exhaustiveness.md](pattern_matching_exhaustiveness.md) | Exhaustiveness checking | Design |
| [type_inference_algorithm.md](type_inference_algorithm.md) | Hindley-Milner type inference | Design |
| [contract_system_design.md](contract_system_design.md) | Pre/postconditions, invariants | Design |
| [effect_system_design.md](effect_system_design.md) | Effect tracking (async, GC, etc) | Design |

### Physics & ML Integration (2 documents + subdirectory)

| Document | Topic | Status |
|----------|-------|--------|
| [pytorch_wrapper_integration.md](pytorch_wrapper_integration.md) | PyTorch FFI wrapper | Design |
| [ml_physics_integration.md](ml_physics_integration.md) | ML-accelerated physics | Research |
| [physics/](physics/) | Physics simulation research | Subdirectory |

### Tooling & Development (4 documents)

| Document | Topic | Status |
|----------|-------|--------|
| [lsp_architecture.md](lsp_architecture.md) | Language Server Protocol impl | Design |
| [formatter_architecture.md](formatter_architecture.md) | Code formatter design | Design |
| [unified_coverage_plan.md](unified_coverage_plan.md) | Test coverage strategy | Plan |
| [lean_verification_with_aop.md](lean_verification_with_aop.md) | Formal verification with Lean 4 | Research |

### Module System (3 documents)

| Document | Topic | Status |
|----------|-------|--------|
| [module_resolution_algorithm.md](module_resolution_algorithm.md) | Import resolution strategy | Design |
| [package_manager_design.md](package_manager_design.md) | UV-style package manager | Design |
| [stdlib_organization.md](stdlib_organization.md) | Standard library structure | Design |

---

## Subdirectories

### api_design/
Detailed API design guidelines organized by topic:
- Naming conventions
- Error handling patterns
- Resource management
- Async API design
- FFI boundaries

See [api_design/README.md](api_design/README.md) for details.

### physics/
Physics simulation integration research:
- Genesis physics engine
- Isaac Gym integration
- ML-accelerated physics
- API design for physics simulation

See [physics/README.md](physics/README.md) for details.

---

## Document Status Legend

| Status | Meaning |
|--------|---------|
| **Research** | Exploratory document, investigating options |
| **Analysis** | Comparison or evaluation of approaches |
| **Design** | Design document with proposed implementation |
| **Plan** | Implementation plan or roadmap |
| **Specification** | Formal specification (consider moving to doc/spec/) |
| **Retrospective** | Lessons learned, post-mortem analysis |
| **Overview** | High-level summary pointing to other docs |
| **Reference** | Comprehensive reference document |

---

## Related Documentation

- **[doc/design/](../design/)** — Design documents (where research conclusions land)
- **[doc/adr/](../adr/)** — Architecture Decision Records (extracted from design)
- **[doc/plan/](../plan/)** — Implementation roadmaps
- **[doc/requirement/](../requirement/)** — Functional requirements that drive research topics
- **[doc/architecture/](../architecture/)** — Architecture principles
- **[doc/spec/](../spec/)** — Stable language specifications

---

## Contributing Research

When adding new research documents:
1. Use descriptive names (topic + subtopic, e.g., `actor_runtime_policy.md`)
2. Add metadata header: Purpose, Status, Last Updated
3. Update this README in the appropriate category
4. Consider creating subdirectories for related topics (5+ files)
5. Link to related specs/status/plans documents

**Avoid:**
- Splitting documents into part1/part2 (merge into single file)
- Session notes (those go in `doc/report/`)
- Status tracking (use `doc/feature/` for feature status, `doc/design/` for implementation status)

---

**Total:** 45 markdown files + 2 subdirectories
