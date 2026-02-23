# compiler

Single source of truth for the Simple compiler implementation.

## Current status

- `src/compiler/` is the unified compiler with numbered layers (NN.name/).
- Layer prefix stripped for imports (e.g., `10.frontend/` → `frontend`).

## Bootstrap (C Backend)

```
bin/simple compile --backend=c  →  generates C code into src/compiler_cpp/
cmake + ninja  →  builds C code + runtime  →  bootstrap binary
```

## Layer Structure

| Layer | Purpose |
|-------|---------|
| `00.common/` | Error types, config, effects, visibility, diagnostics, registry |
| `10.frontend/` | Lexer, parser, AST, treesitter, desugar, parser types |
| `15.blocks/` | Block definition system |
| `20.hir/` | HIR types, definitions, lowering |
| `25.traits/` | Trait definition, impl, solver, coherence |
| `30.types/` | Type inference, type system, dimension constraints |
| `35.semantics/` | Semantic analysis, lint, macro check, resolve |
| `40.mono/` | Monomorphization, instantiation |
| `50.mir/` | MIR types, data, instructions, lowering |
| `55.borrow/` | Borrow checking, GC analysis |
| `60.mir_opt/` | MIR optimization passes |
| `70.backend/` | Backends (C, LLVM, Cranelift, WASM, CUDA, etc.), linker |
| `80.driver/` | Driver, pipeline, project, build mode |
| `85.mdsoc/` | MDSOC (virtual capsules, feature, transform, weaving) |
| `90.tools/` | API surface, coverage, query, AOP |
| `95.interp/` | Interpreter, MIR interpreter |
| `99.loader/` | Module resolver, loader |

## Rules

- Lower-numbered layers cannot depend on higher-numbered layers
- No circular dependencies between modules
