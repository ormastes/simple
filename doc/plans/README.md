# Implementation Plans

**Purpose:** Sequential roadmap and major initiative plans for Simple language development.

**Last Updated:** 2025-12-28

---

## Overview

This directory contains two types of implementation plans:

1. **Numbered Plans** (01-30+) - Sequential development roadmap
2. **Named Initiatives** (UPPERCASE) - Major cross-cutting features

---

## Plan Types

### Numbered Plans (01_*.md through 30+_*.md)

Sequential roadmap for core language features. Each numbered plan represents a development milestone.

**Naming Convention:** `{number}_{brief_description}.md`

**Examples:**
- `01_dynlib_format_suggestion.md` - Dynamic library format design
- `02_parser_implementation.md` - Parser implementation plan
- `05_ahead_of_time_compile.md` - AOT compilation milestone

**Note:** Some plans have `_2` suffixes indicating revised versions:
- Original: `01_dynlib_format_suggestion.md`
- Revised: `01_dynlib_format_suggestion_2.md`

The `_2` version usually supersedes the original but both are kept for reference.

### Major Initiatives (UPPERCASE_*.md)

Cross-cutting features that span multiple milestones.

**Naming Convention:** `UPPERCASE_TOPIC_PLAN.md`

**Examples:**
- `VULKAN_BACKEND_PLAN.md` - Vulkan GPU backend
- `ML_PYTORCH_PHYSICS_IMPLEMENTATION.md` - ML/Physics integration
- `PYTORCH_GENESIS_IMPLEMENTATION.md` - Genesis physics engine

These represent significant undertakings that may run parallel to numbered milestones.

---

## Numbered Roadmap (Active Plans)

### Foundation (01-10)

| # | Plan | Status | Description |
|---|------|--------|-------------|
| 01 | dynlib_format_suggestion | ✅ Complete | Dynamic library format (SMF) |
| 02 | parser_implementation | ✅ Complete | Parser and AST |
| 03 | basic_io_library | ✅ Complete | Basic I/O operations |
| 04 | dynamic_loading_library | ✅ Complete | Dynamic module loading |
| 05 | ahead_of_time_compile | ✅ Complete | AOT compilation (Cranelift) |
| 06 | dynamic_reload | ✅ Complete | Hot reload support |
| 07 | basic_types | ✅ Complete | Type system basics |
| 08 | function_lib_call | ✅ Complete | Function calls and FFI |
| 09 | stdlib_units_and_networking | 🔨 In Progress | Standard library expansion |
| 10 | std_print_migration | ✅ Complete | Print statement migration |

### Core Features (11-20)

| # | Plan | Status | Description |
|---|------|--------|-------------|
| 11 | test_file_separation | ✅ Complete | Test organization |
| 12 | compile_to_binary | ✅ Complete | Binary compilation |
| 13 | simple_test_framework | ✅ Complete | BDD test framework |
| 14 | build_target | 🔨 In Progress | Build system |
| 15 | macros | ✅ Complete | Macro system |
| 16 | codegen_switch_call | ✅ Complete | Codegen optimization |
| 17 | dependency_injection | ✅ Complete | DI container |
| 18 | doctest | ✅ Complete | Documentation testing |
| 19 | ml_pytorch_physics | 🔨 In Progress | ML/Physics integration |
| 20 | lean_verification | 📋 Planned | Formal verification |

### Advanced (21-30)

| # | Plan | Status | Description |
|---|------|--------|-------------|
| 21 | 3d_engine_core | 🔨 In Progress | 3D graphics engine |
| 22 | simple_math | 📋 Planned | Mathematical library |
| 23+ | (future plans) | 📋 Planned | TBD |

---

## Major Initiatives

### GPU & Graphics

| Plan | Status | Description |
|------|--------|-------------|
| VULKAN_BACKEND_PLAN.md | 🔨 In Progress | Vulkan compute & graphics backend |
| 3D_ENGINE_IMPLEMENTATION.md | 🔨 In Progress | 3D rendering engine |
| GPU_SIMD_UNIFIED_BACKEND.md | 📋 Planned | Unified GPU/SIMD execution |

### ML & Physics

| Plan | Status | Description |
|------|--------|-------------|
| ML_PYTORCH_PHYSICS_IMPLEMENTATION.md | 🔨 In Progress | PyTorch wrapper + physics |
| PYTORCH_GENESIS_IMPLEMENTATION.md | 🔨 In Progress | Genesis physics engine integration |
| PHYSICS_SIMULATION_PLAN.md | 📋 Planned | Physics simulation framework |

### Language Features

| Plan | Status | Description |
|------|--------|-------------|
| METAPROGRAMMING_COMPLETE.md | ✅ Complete | Macro system completion |
| AOP_DI_COMPLETE.md | ✅ Complete | AOP + DI integration |
| CONTRACT_SYSTEM_PLAN.md | 🔨 In Progress | Pre/postconditions, invariants |

### Tooling

| Plan | Status | Description |
|------|--------|-------------|
| VSCODE_EXTENSION_PLAN.md | 🔨 In Progress | VSCode language support |
| LSP_IMPLEMENTATION_PLAN.md | 📋 Planned | Language Server Protocol |
| FORMATTER_LINTER_PLAN.md | ✅ Complete | Code formatting & linting |

---

## Plan Status Legend

| Status | Symbol | Meaning |
|--------|--------|---------|
| Complete | ✅ | Fully implemented and tested |
| In Progress | 🔨 | Active development |
| Planned | 📋 | Scheduled but not started |
| On Hold | ⏸️ | Paused pending dependencies |
| Superseded | ⚠️ | Replaced by newer plan |

---

## Duplicate Files (_2 suffix)

Some plans have `_2` versions indicating revisions:

| Original | Revised | Recommendation |
|----------|---------|----------------|
| 01_dynlib_format_suggestion.md | 01_dynlib_format_suggestion_2.md | Use _2 version |
| 04_dynamic_loading_library.md | 04_dynamic_loading_library_2.md | Use _2 version |
| 07_basic_types.md | 07_basic_types_2.md | Use _2 version |
| 08_function_lib_call.md | 08_function_lib_call_2.md | Use _2 version |

**Recommendation:** Archive or delete non-_2 versions if _2 is the active plan.

---

## Related Documentation

- **[doc/spec/](../spec/)** - Language specifications
- **[doc/research/](../research/)** - Technical research
- **[doc/status/](../status/)** - Implementation status tracking
- **[doc/features/](../features/)** - Feature catalog

---

## Adding New Plans

### For Numbered Plans:
1. Find the next available number
2. Use descriptive name: `{number}_{feature_name}.md`
3. Include: Goal, Dependencies, Implementation Steps, Testing
4. Update this README roadmap section

### For Major Initiatives:
1. Use UPPERCASE naming: `INITIATIVE_NAME_PLAN.md`
2. Include: Overview, Phases, Dependencies, Timeline (no dates, just sequence)
3. Link to related numbered plans
4. Update this README initiatives section

---

**Total:** 55 implementation plans (36 numbered + 19 initiatives)
