# Simple Language Specification

> **🎯 MIGRATION COMPLETE:** Core language specifications have been migrated to executable test files!
> **See:** [tests/specs/](../../tests/specs/) for all _spec.spl files

**Quick Links:** [Core](#core-language) | [Advanced](#advanced-features) | [Testing](#testing--quality) | [Tooling](#tooling--development) | [Parser](#parser-implementation) | [GPU](#gpu--graphics) | [UI](#ui--interfaces) | [Formats](#data-formats) | **[Migrated Specs](#migrated-specifications)**

---

## Migrated Specifications

### ✅ Category A: Direct Migrations (Replaced)

These specs have been completely migrated to executable test files. The original .md files remain for reference but are superseded by the _spec.spl files.

| Original File | _spec.spl File | Status | Examples |
|--------------|----------------|--------|----------|
| [syntax.md](language/syntax.md) | [syntax_spec.spl](../../tests/specs/syntax_spec.spl) | ⚠️ Migrated | 21 |
| [types.md](language/types.md) | [types_spec.spl](../../tests/specs/types_spec.spl) | ⚠️ Migrated | 17 |
| [type_inference.md](language/type_inference.md) | [type_inference_spec.spl](../../tests/specs/type_inference_spec.spl) | ⚠️ Migrated | 24 |
| [async_default.md](language/async_default.md) | [async_default_spec.spl](../../tests/specs/async_default_spec.spl) | ⚠️ Migrated | 37 |
| [suspension_operator.md](language/suspension_operator.md) | [suspension_operator_spec.spl](../../tests/specs/suspension_operator_spec.spl) | ⚠️ Migrated | 24 |
| [capability_effects.md](language/capability_effects.md) | [capability_effects_spec.spl](../../tests/specs/capability_effects_spec.spl) | ⚠️ Migrated | 14 |
| [sandboxing.md](language/sandboxing.md) | [sandboxing_spec.spl](../../tests/specs/sandboxing_spec.spl) | ⚠️ Migrated | 0 |

**Totals:** 7 specs migrated, 137 examples

### 📤 Category B: Extracted Tests (Reference Kept)

These specs remain as architectural reference documentation. Test cases have been extracted to _spec.spl files for validation.

| Reference Doc | _spec.spl File | Status | Examples |
|--------------|----------------|--------|----------|
| [functions.md](language/functions.md) | [functions_spec.spl](../../tests/specs/functions_spec.spl) | 📤 Extracted | 24 |
| [traits.md](language/traits.md) | [traits_spec.spl](../../tests/specs/traits_spec.spl) | 📤 Extracted | 36 |
| [memory.md](language/memory.md) | [memory_spec.spl](../../tests/specs/memory_spec.spl) | 📤 Extracted | 17 |
| [modules.md](language/modules.md) | [modules_spec.spl](../../tests/specs/modules_spec.spl) | 📤 Extracted | 0 |
| [data_structures.md](language/data_structures.md) | [data_structures_spec.spl](../../tests/specs/data_structures_spec.spl) | 📤 Extracted | 32 |
| [concurrency.md](language/concurrency.md) | [concurrency_spec.spl](../../tests/specs/concurrency_spec.spl) | 📤 Extracted | 24 |
| [macro.md](language/macro.md) | [macro_spec.spl](../../tests/specs/macro_spec.spl) | 📤 Extracted | 0 |
| [metaprogramming.md](language/metaprogramming.md) | [metaprogramming_spec.spl](../../tests/specs/metaprogramming_spec.spl) | 📤 Extracted | 24 |

**Totals:** 8 specs extracted, 157 examples

**See Also:**
- [Spec Quick Reference](SPEC_QUICK_REF.md) - How to write _spec.spl files

---

## Status Legend

- ✅ **Stable** - Complete spec + implementation
- 🔨 **Implementing** - Complete spec, partial implementation
- 📝 **Draft** - Spec under development
- 🔄 **Evolving** - Implemented but spec changing
- ⚠️ **Deprecated** - Superseded, kept for reference
- 📚 **Reference** - Supporting docs, not normative

---

## Core Language (10 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [Syntax](language/syntax.md) | ✅ | #10-19 | Execution modes, lexical structure, operators |
| [Types](language/types.md) | ✅ | #20-29 | Type system, mutability, unit types |
| [Type Inference](language/type_inference.md) | ✅ | #13 | Hindley-Milner type inference, unification |
| [Units](language/units.md) | 🔨 | #30-34 | Semantic unit types |
| [Data Structures](language/data_structures.md) | ✅ | #35-39 | Structs, classes, enums, unions |
| [Functions](language/functions.md) | ✅ | #40-44 | Functions, pattern matching, constructors |
| [Traits](language/traits.md) | ✅ | #45-49 | Traits, implementations, polymorphism |
| [Memory](language/memory.md) | ✅ | #50-54 | Ownership, borrowing, pointer types |
| [Modules](language/modules.md) | 🔨 | #55-59 | Import/export system |

---

## Advanced Features (10 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [Concurrency](language/concurrency.md) | 🔨 | #65-74 | Actors, async/await, futures |
| [Async Default](language/async_default.md) | 📝 | #276-285 | Async-by-default, explicit sync |
| [Suspension Operator](language/suspension_operator.md) | 📝 | #270-275 | Explicit `~` suspension syntax |
| [Metaprogramming](language/metaprogramming.md) | ✅ | #75-84 | Macros, decorators, comprehensions |
| [Macro System](language/macro.md) | 🔨 | #400-450 | Advanced macro specification |
| [Capability Effects](language/capability_effects.md) | 📝 | #100-110 | Reference capabilities |
| [Standard Library](language/stdlib.md) | 🔨 | #85-99 | Stdlib organization |

---

## Testing & Quality (8 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [SSpec Guide](language/sspec_guide.md) | ✅ | - | **Complete user guide for SSpec** |
| [Doctest](testing/sdoctest.md) | ✅ | #303 | Documentation testing |
| [Doctest README](testing/doctest_readme.md) | ✅ | #303 | README.md-based doctest discovery |
| [Mock Framework](testing/mock.md) | ✅ | - | Test doubles and mocking |
| [Property Testing](testing/property_testing.md) | 📝 | - | Property-based testing |
| [Snapshot Testing](testing/snapshot_testing.md) | 📝 | - | Snapshot regression testing |
| [Semantic Diff](testing/semantic_diff.md) | 📝 | - | Semantic code comparison |

---

## Tooling & Development (5 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [Formatter](tooling/formatter.md) | ✅ | #800-810 | Code formatting |
| [Linting Rules](tooling/formatting_lints.md) | 🔨 | #811-825 | Linter rules |
| [Build Audit](tooling/build_audit.md) | 📝 | #826-835 | Build auditing |
| [VSCode Extension](tooling/vscode_extension.md) | 🔨 | #836-845 | VSCode support |
| [MCP Integration](tooling/basic_mcp.md) | 🔨 | #846-855 | Model Context Protocol |

---

## Parser Implementation (3 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [Overview](parser/overview.md) | ✅ | - | Parser architecture |
| [Grammar](parser/lexer_parser_grammar.md) | ✅ | - | Formal grammar |
| [Grammar Reference](grammar/grammar_reference.md) | ✅ | - | Grammar reference and keywords |

---

## GPU & Graphics (13 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [GPU & SIMD](gpu_simd/README.md) | 🔨 | #300-350 | GPU compute, SIMD overview |
| [GPU Kernels](gpu_simd/kernels.md) | 🔨 | #310-320 | Kernel programming |
| [SIMD Operations](gpu_simd/simd.md) | 🔨 | #330-340 | SIMD vector operations |
| [GPU Spec](gpu_simd/gpu.md) | 🔨 | #300-309 | GPU programming model |
| [Optimizations](gpu_simd/optimization.md) | 📝 | #341-350 | Performance optimization |
| [3D Graphics](graphics_3d/README.md) | 🔨 | #500-550 | 3D rendering overview |
| [Scene Graph](graphics_3d/scene_graph.md) | 🔨 | #510-520 | Scene hierarchy |
| [Materials](graphics_3d/materials.md) | 🔨 | #521-525 | Material system |
| [Rendering](graphics_3d/rendering.md) | 🔨 | #526-535 | Rendering pipeline |
| [Resources](graphics_3d/resources.md) | 🔨 | #536-540 | Resource management |
| [Examples](graphics_3d/examples.md) | 📝 | - | 3D examples |
| [Appendices](graphics_3d/appendices.md) | 📚 | - | Additional info |

---

## UI & Interfaces (3 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [TUI Framework](language/tui.md) | 🔨 | #600-650 | Terminal UI |
| [Web Framework](language/web.md) | 📝 | #700-750 | Web framework |
| [Sandboxing](language/sandboxing.md) | 🔨 | #916-923 | Runtime & environment isolation |

---

## Finding Related Specs

### By Topic (Navigation Paths)

**Type System:**
```
language/types.md → language/units.md → language/data_structures.md
```

**Memory Management:**
```
language/memory.md → language/capability_effects.md → language/concurrency.md
```

**Async/Concurrency:**
```
language/concurrency.md → language/async_default.md → language/suspension_operator.md → language/capability_effects.md
```

**Macros:**
```
language/macro.md → language/metaprogramming.md
```

**Testing:**
```
testing/sdoctest.md → testing/doctest_readme.md → testing/mock.md
```

**GPU Programming:**
```
gpu_simd/README.md → gpu_simd/gpu.md → gpu_simd/kernels.md → gpu_simd/optimization.md
```

**3D Graphics:**
```
graphics_3d/README.md → graphics_3d/scene_graph.md → graphics_3d/rendering.md
```

### By Status

**Stable (Ready to Use):**
- language/syntax, language/types, language/data_structures, language/functions, language/traits, language/memory
- testing/sdoctest, testing/mock
- tooling/formatter

**Implementing (Work in Progress):**
- language/modules, language/macro, language/concurrency, language/stdlib
- gpu_simd/*, graphics_3d/*, language/tui, language/sandboxing
- tooling/formatting_lints, tooling/vscode_extension, tooling/basic_mcp

**Draft (Planning Phase):**
- language/capability_effects, testing/property_testing, testing/snapshot_testing
- tooling/build_audit, language/web

### By Feature ID Range

**#10-49: Core language**
- syntax, types, units, data_structures, functions, traits, memory, modules

**#50-99: Extended core**
- memory (#50-54), modules (#55-59), concurrency (#65-74), metaprogramming (#75-84), stdlib (#85-99)

**#100-110: Capability effects**
- capability_effects

**#300-399: GPU & SIMD**
- gpu_simd/* (#300-350)

**#400-499: Macros**
- macro (#400-450)

**#500-599: Graphics & UI**
- graphics_3d/* (#500-550), tui (#600-650)

**#700-750: Web**
- web (#700-750)

**#800-899: Tooling**
- formatter (#800-810), formatting_lints (#811-825), build_audit (#826-835), vscode_extension (#836-845), basic_mcp (#846-855)

**#900-999: Sandboxing**
- sandboxing (#916-923)

---

## Quick Start Guides

### I want to understand the type system
1. Start: [Types](language/types.md) - Core type system
2. Next: [Units](language/units.md) - Semantic unit types
3. Then: [Data Structures](language/data_structures.md) - Composite types
4. Advanced: [Capability Effects](language/capability_effects.md) - Reference capabilities

### I want to write tests
1. **Start: [SSpec Guide](language/sspec_guide.md) - Complete user guide**
2. Next: [Doctest](testing/sdoctest.md) - Inline documentation tests
3. Then: [Mock Framework](testing/mock.md) - Test doubles

### I want to do GPU programming
1. Start: [GPU & SIMD](gpu_simd/README.md) - Overview and philosophy
2. Next: [GPU Spec](gpu_simd/gpu.md) - GPU programming model
3. Then: [Kernels](gpu_simd/kernels.md) - Writing kernels
4. Advanced: [Optimizations](gpu_simd/optimization.md) - Performance tuning

### I want to build 3D graphics
1. Start: [3D Graphics](graphics_3d/README.md) - Overview
2. Next: [Scene Graph](graphics_3d/scene_graph.md) - Scene hierarchy
3. Then: [Rendering](graphics_3d/rendering.md) - Rendering pipeline
4. Advanced: [Materials](graphics_3d/materials.md) - Material system

### I want to create a language tool
1. Start: [Parser Overview](parser/overview.md) - Parser architecture
2. Next: [Grammar](parser/lexer_parser_grammar.md) - Token types and grammar
3. Then: [VSCode Extension](tooling/vscode_extension.md) - IDE integration

---

## Document Conventions

All spec files should include this metadata header:

```markdown
# [Title]

**Status:** [Stable|Implementing|Draft|Evolving|Deprecated|Reference]
**Feature IDs:** #XXX-YYY
**Last Updated:** YYYY-MM-DD
**Keywords:** keyword1, keyword2, keyword3
**Topics:** topic-tag1, topic-tag2

[Brief description]

## Related Specifications
- [Spec 1](path.md) - Relationship description
- [Spec 2](path.md) - Relationship description

---

[Content]
```

### Cross-Reference Guidelines

1. **Use relative links:** `[Types](types.md)` not `/doc/spec/types.md`
2. **Descriptive text:** `[Type System](types.md)` not `[here](types.md)`
3. **Section anchors:** `[Mutability Rules](types.md#mutability-summary)`
4. **Subdirectories:** `[Parser Overview](parser/overview.md)`

### Topic Tags

Use 2-4 tags from this vocabulary:
- `memory-safety`, `concurrency`, `type-system`, `metaprogramming`
- `testing`, `gpu`, `io`, `tooling`, `syntax`, `runtime`, `security`

---

## Relationship Diagrams

### Core Foundation
```
language/syntax.md → language/types.md → language/functions.md → language/traits.md
                            ↓
                     language/units.md
```

### Memory & Safety
```
language/memory.md → language/capability_effects.md → language/concurrency.md
```

### Testing Stack
```
testing/sdoctest.md
       ↓
testing/mock.md
```

### GPU Stack
```
gpu_simd/README.md → gpu_simd/gpu.md → gpu_simd/kernels.md
                                              ↓
                                    gpu_simd/optimization.md
```

---

## See Also

- [Language Specs](language/) - Core language specifications
- [Feature Index](../features/feature.md) - Complete feature catalog
- [Implementation Status](../status/) - Per-feature implementation status
- [Architecture](../architecture/overview.md) - System architecture

---

## Total Specifications

- **Core Language:** 9 specs
- **Advanced Features:** 7 specs
- **Testing & Quality:** 7 specs
- **Tooling & Development:** 5 specs
- **Parser Implementation:** 3 specs
- **GPU & Graphics:** 13 specs
- **UI & Interfaces:** 3 specs

**Total:** 47 specification documents

---

*Last updated: 2026-01-09*
*For questions or improvements, see [CLAUDE.md](../../CLAUDE.md)*
