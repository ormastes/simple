# Layered Compiler Architecture

**Status:** Design
**Last Updated:** 2026-02-20

---

## Overview

The `src/compiler/` directory is restructured into numbered layer directories where the numeric prefix defines compilation layer ordering. The convention `NN.name/` uses a 2-digit prefix for ordering and the `name` portion for package identity in module resolution.

Module resolution strips the numeric prefix: `use compiler.frontend.X` resolves through `10.frontend/X.spl`.

---

## Layer Numbering Convention

- Directories use the pattern `NN.name/` where `NN` is a 2-digit number (00–99)
- The `NN.` prefix is stripped during module resolution — `10.frontend/` is the `frontend` package
- Layer N can import layers <= N only (lower or equal numbered layers)
- `00.common` is importable by all layers (it is the lowest)
- Within a layer, files can freely import each other
- Gaps between numbers allow future insertion (e.g., 15, 25, 35, etc.)

---

## Layer Assignments

| Dir | Package | Layer | Contents |
|-----|---------|-------|----------|
| `00.common/` | `common` | 0 | Error types, config, effects, visibility, compilation context, compiler services, GC config, parallel, unsafe, volatile, predicates, `dependency/`, `diagnostics/`, `registry/` |
| `10.frontend/` | `frontend` | 10 | `core/` (lexer, parser, AST, tokens), `treesitter/`, `parser/`, `desugar/`, parser types, frontend entry |
| `15.blocks/` | `blocks` | 15 | Block definition system (22 files) |
| `20.hir/` | `hir` | 20 | HIR types, definitions, `hir_lowering/` (6 files), `inference/` |
| `25.traits/` | `traits` | 25 | Trait definition, implementation, solver, coherence, validation, method resolution |
| `30.types/` | `types` | 30 | `type_infer/` (7), `type_system/` (10), type layout, dimension constraints, phase files (bidir, associated types, higher rank poly, variance, macro checker, const keys, SIMD) |
| `35.semantics/` | `semantics` | 35 | `semantics/`, `lint/`, `macro_check/`, resolve, pattern analysis, const eval, comptime checker, safety checker, verification checker, SIMD check |
| `40.mono/` | `mono` | 40 | `monomorphize/` (18), monomorphize integration, instantiation |
| `50.mir/` | `mir` | 50 | MIR types, data, instructions, lowering (5 files), JSON, contract, bitfield, effects, serialization |
| `55.borrow/` | `borrow` | 55 | `borrow_check/`, `gc_analysis/` |
| `60.mir_opt/` | `mir_opt` | 60 | `mir_opt/` (17), MIR optimization integration |
| `70.backend/` | `backend` | 70 | All backends (LLVM, C, Cranelift, WASM, CUDA, Vulkan, VHDL, Lean, Native, common), build native, calling convention, target presets, link attrs, arch rules, inline asm, GPU intrinsics, FFI, `linker/` |
| `80.driver/` | `driver` | 80 | Driver, driver types, pipeline, `driver/`, `pipeline/`, project, build mode/log, incremental, hydration manifest, layout recorder, SMF writer |
| `85.mdsoc/` | `mdsoc` | 85 | `mdsoc/`, `feature/`, `transform/`, `weaving/`, `adapters/` |
| `90.tools/` | `tools` | 90 | API surface, coverage, query API, symbol analyzer, context pack, suffix registry, AOP, async integration, desugar async, semantic diff |
| `95.interp/` | `interp` | 95 | `interpreter/`, MIR interpreter, `execution/` |
| `99.loader/` | `loader` | 99 | `loader/`, `module_resolver/` |

---

## Layer Dependency Rule

A module in layer N may only import modules from layers with number <= N.

```
Layer 99 (loader)  → can import layers 0–99
Layer 95 (interp)  → can import layers 0–95
Layer 80 (driver)  → can import layers 0–80
Layer 70 (backend) → can import layers 0–70
Layer 50 (mir)     → can import layers 0–50
Layer 10 (frontend)→ can import layers 0–10
Layer 00 (common)  → can import layer 0 only
```

This rule is enforced by `check_numbered_layer_dep()` in `src/compiler/mdsoc/layer_checker.spl`.

---

## Numeric Prefix Stripping

The module resolver strips `NN.` prefixes during resolution:

1. Given import `use compiler.frontend.parser_types`
2. Resolver looks for `src/compiler/frontend/` — not found
3. Resolver scans `src/compiler/` for directories matching `*.frontend/`
4. Finds `src/compiler/10.frontend/` — strips `10.` prefix, matches `frontend`
5. Resolves to `src/compiler/10.frontend/parser_types.spl`

This is implemented via `find_numbered_dir()` helper in `module_resolver/resolution.spl`.

---

## `__init__.spl` Per Layer

Each numbered directory has an `__init__.spl` that declares:
- Module identity (`mod <name>`)
- Public submodules (`pub mod X`)
- Exports (`export Symbol1, Symbol2`)
- Friend declarations (`friend <package>`) — see `friend_access_control.md`
- Internal exports (`internal_export Symbol`) — friend-visible symbols
- Common imports (`common use ...`)

---

## Import Patterns

### Qualified imports (preferred)
```simple
use compiler.frontend.parser_types.{ParseResult, Token}
use compiler.mir.mir_data.{MirFunction, MirBlock}
```

### Cross-layer imports
```simple
# Layer 50 (mir) importing from layer 10 (frontend) — allowed (50 > 10)
use compiler.frontend.core.ast.{AstNode}

# Layer 10 (frontend) importing from layer 50 (mir) — VIOLATION (10 < 50)
# use compiler.mir.mir_data.{MirFunction}  # ERROR: layer 10 cannot import layer 50
```

### Same-layer imports
```simple
# Within layer 50 (mir), files can import each other freely
use compiler.mir.mir_types.{MirType}
use compiler.mir.mir_instructions.{MirInst}
```

---

## See Also

- [Friend Access Control](friend_access_control.md) — `friend` declarations and visibility modifiers
- [Syntax Quick Reference](../guide/syntax_quick_reference.md) — language syntax
