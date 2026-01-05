# Simple Language Specification

**Quick Links:** [Core](#core-language) | [Advanced](#advanced-features) | [Testing](#testing--quality) | [Tooling](#tooling--development) | [Parser](#parser-implementation) | [GPU](#gpu--graphics) | [UI](#ui--interfaces) | [Formats](#data-formats)

---

## Status Legend

- ✅ **Stable** - Complete spec + implementation
- 🔨 **Implementing** - Complete spec, partial implementation
- 📝 **Draft** - Spec under development
- 🔄 **Evolving** - Implemented but spec changing
- ⚠️ **Deprecated** - Superseded, kept for reference
- 📚 **Reference** - Supporting docs, not normative

---

## Core Language (9 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [Syntax](syntax.md) | ✅ | #10-19 | Execution modes, lexical structure, operators |
| [Types](types.md) | ✅ | #20-29 | Type system, mutability, unit types |
| [Units](units.md) | 🔨 | #30-34 | Semantic unit types |
| [Data Structures](data_structures.md) | ✅ | #35-39 | Structs, classes, enums, unions |
| [Functions](functions.md) | ✅ | #40-44 | Functions, pattern matching, constructors |
| [Traits](traits.md) | ✅ | #45-49 | Traits, implementations, polymorphism |
| [Memory](memory.md) | ✅ | #50-54 | Ownership, borrowing, pointer types |
| [Modules](modules.md) | 🔨 | #55-59 | Import/export system |
| [Primitive as Object](primitive_as_obj.md) | 🔄 | #60-64 | Primitive type methods |

---

## Advanced Features (10 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [Concurrency](concurrency.md) | 🔨 | #65-74 | Actors, async/await, futures |
| [Async Default](async_default.md) | 📝 | #276-285 | Async-by-default, explicit sync |
| [Suspension Operator](suspension_operator.md) | 📝 | #270-275 | Explicit `~` suspension syntax |
| [Metaprogramming](metaprogramming.md) | ✅ | #75-84 | Macros, decorators, comprehensions |
| [Macro System](macro.md) | 🔨 | #400-450 | Advanced macro specification |
| [Invariants](invariant.md) | 🔨 | #451-470 | Contracts and invariants |
| [Capability Effects](capability_effects.md) | 📝 | #100-110 | Reference capabilities |
| [FFI & ABI](ffi_abi.md) | 🔨 | #200-210 | Foreign function interface |
| [Standard Library](stdlib.md) | 🔨 | #85-99 | Stdlib organization |
| [File I/O](file_io.md) | 🔨 | #211-220 | File operations |

---

## Testing & Quality (6 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [BDD Framework](testing/testing_bdd_framework.md) | ✅ | #302 | BDD testing, matchers, Gherkin |
| [Doctest](testing/sdoctest.md) | ✅ | #303 | Documentation testing |
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

## Parser Implementation (8 specs)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [Overview](parser/overview.md) | ✅ | - | Parser architecture |
| [Lexer & Parser](lexer_parser.md) | ✅ | - | Token types, grammar |
| [Incremental](parser/incremental.md) | 📝 | - | Incremental parsing |
| [Error Recovery](parser/error_recovery.md) | 📝 | - | Parse error recovery |
| [Grammar](parser/lexer_parser_grammar.md) | ✅ | - | Formal grammar |
| [Operator Precedence](parser/precedence.md) | ✅ | - | Precedence rules |
| [Indentation](parser/indentation.md) | ✅ | - | INDENT/DEDENT handling |

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
| [TUI Framework](tui.md) | 🔨 | #600-650 | Terminal UI |
| [Web Framework](web.md) | 📝 | #700-750 | Web framework |
| [Sandboxing](sandboxing.md) | 🔨 | #916-923 | Runtime & environment isolation |

---

## Data Formats (1 spec)

| Spec | Status | Feature IDs | Description |
|------|--------|-------------|-------------|
| [SDN](sdn.md) | ✅ | #600-610 | Simple Data Notation |

---

## Finding Related Specs

### By Topic (Navigation Paths)

**Type System:**
```
types.md → units.md → primitive_as_obj.md → data_structures.md
```

**Memory Management:**
```
memory.md → capability_effects.md → concurrency.md
```

**Async/Concurrency:**
```
concurrency.md → async_default.md → suspension_operator.md → capability_effects.md
```

**Macros:**
```
macro.md → metaprogramming.md → invariant.md
```

**Testing:**
```
testing/testing_bdd_framework.md → testing/sdoctest.md → testing/mock.md
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
- syntax, types, data_structures, functions, traits, memory
- testing/testing_bdd_framework, testing/sdoctest, testing/mock
- tooling/formatter, sdn

**Implementing (Work in Progress):**
- modules, macro, concurrency, stdlib, file_io
- gpu_simd/*, graphics_3d/*, tui, sandboxing
- tooling/formatting_lints, tooling/vscode_extension, tooling/basic_mcp

**Draft (Planning Phase):**
- capability_effects, testing/property_testing, testing/snapshot_testing
- tooling/build_audit, web

### By Feature ID Range

**#10-49: Core language**
- syntax, types, units, data_structures, functions, traits, memory, modules, primitive_as_obj

**#50-99: Extended core**
- memory (#50-54), modules (#55-59), primitive_as_obj (#60-64), concurrency (#65-74), metaprogramming (#75-84), stdlib (#85-99)

**#100-110: Capability effects**
- capability_effects

**#200-220: FFI & I/O**
- ffi_abi (#200-210), file_io (#211-220)

**#300-399: GPU & SIMD**
- gpu_simd/* (#300-350)

**#400-499: Contracts**
- macro (#400-450), invariant (#451-470)

**#500-599: Graphics & UI**
- graphics_3d/* (#500-550), tui (#600-650)

**#600-610: Data formats**
- sdn (#600-610)

**#700-750: Web**
- web (#700-750)

**#800-899: Tooling**
- formatter (#800-810), formatting_lints (#811-825), build_audit (#826-835), vscode_extension (#836-845), basic_mcp (#846-855)

**#900-999: Sandboxing**
- sandboxing (#916-923)

---

## Quick Start Guides

### I want to understand the type system
1. Start: [Types](types.md) - Core type system
2. Next: [Units](units.md) - Semantic unit types
3. Then: [Data Structures](data_structures.md) - Composite types
4. Advanced: [Capability Effects](capability_effects.md) - Reference capabilities

### I want to write tests
1. Start: [BDD Framework](testing/testing_bdd_framework.md) - Test framework overview
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
2. Next: [Lexer & Parser](lexer_parser.md) - Token types and grammar
3. Then: [VSCode Extension](tooling/vscode_extension.md) - IDE integration
4. Advanced: [LSP](../status/lsp_implementation.md) - Language Server Protocol

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
syntax.md → types.md → functions.md → traits.md
               ↓
          units.md → primitive_as_obj.md
```

### Memory & Safety
```
memory.md → capability_effects.md → concurrency.md
                       ↓
                 invariant.md
```

### Testing Stack
```
testing/testing_bdd_framework.md
       ↓
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

- [Language Overview](language.md) - Legacy index (being phased out)
- [Feature Index](../features/feature.md) - Complete feature catalog
- [Implementation Status](../status/) - Per-feature implementation status
- [Architecture](../architecture/overview.md) - System architecture

---

## Total Specifications

- **Core Language:** 9 specs
- **Advanced Features:** 10 specs
- **Testing & Quality:** 6 specs
- **Tooling & Development:** 5 specs
- **Parser Implementation:** 8 specs
- **GPU & Graphics:** 13 specs
- **UI & Interfaces:** 3 specs
- **Data Formats:** 1 spec

**Total:** 55 specification documents

---

*Last updated: 2026-01-05*
*For questions or improvements, see [CLAUDE.md](../../CLAUDE.md)*
