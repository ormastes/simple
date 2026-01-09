# Architecture Skill - Simple Compiler

## Crate Dependency Graph

```
driver (CLI) ─────────────────────────────────┐
    │                                         │
    ├── compiler (HIR, MIR, Codegen) ─────────┤
    │       │                                 │
    │       ├── parser (Lexer, AST) ──────────┤
    │       │       │                         │
    │       │       └── common ───────────────┤
    │       │                                 │
    │       ├── type (Type checker) ──────────┤
    │       │                                 │
    │       └── runtime (GC, Values) ─────────┤
    │               │                         │
    │               └── log ──────────────────┤
    │                                         │
    ├── loader (SMF binary loader) ───────────┤
    │                                         │
    ├── native_loader (OS dylib) ─────────────┤
    │                                         │
    └── pkg (Package manager) ────────────────┘
```

## Compilation Pipeline

```
Source (.spl)
    │
    ▼
┌────────┐
│ Lexer  │ → Tokens (INDENT/DEDENT)
└────────┘
    │
    ▼
┌────────┐
│ Parser │ → AST
└────────┘
    │
    ▼
┌────────┐
│  HIR   │ → Type-checked IR
└────────┘
    │
    ▼
┌────────┐
│  MIR   │ → 50+ instructions
└────────┘
    │
    ├────────────────┐
    ▼                ▼
┌────────┐    ┌────────────┐
│Compiled│    │Interpreter │  (Hybrid execution)
│(Crane- │    │  Fallback  │
│ lift)  │    │            │
└────────┘    └────────────┘
    │                │
    └───────┬────────┘
            ▼
       Execution
```

## Key Directories

### Rust Compiler (`src/`)
```
src/
├── common/      # DynLoader, ConfigEnv (no deps)
├── parser/      # Lexer, Parser, AST
├── type/        # Type checker (HM scaffold)
├── compiler/    # HIR, MIR, Codegen, Interpreter
│   ├── hir/     # High-level IR
│   ├── mir/     # Mid-level IR
│   ├── codegen/ # Cranelift backend
│   └── linker/  # SMF emission
├── runtime/     # GC, RuntimeValue, Actors
├── loader/      # SMF binary loader
├── native_loader/ # OS dylib loader
├── pkg/         # Package manager
└── driver/      # CLI entry point
```

### Simple Language (`simple/`)
```
simple/
├── app/         # Self-hosted tools
│   ├── formatter/
│   ├── lint/
│   ├── lsp/
│   └── dap/
├── std_lib/     # Standard library
│   ├── src/     # .spl source
│   │   ├── core/        # GC + mutable
│   │   ├── core_nogc/   # No GC + mutable
│   │   ├── host/        # OS-based overlays
│   │   └── concurrency/ # Actors, channels
│   └── test/    # BDD tests
└── build/       # Intermediate .smf files
```

## MIR Instruction Categories

| Category | Count | Examples |
|----------|-------|----------|
| Core | 6 | ConstInt, BinOp, UnaryOp |
| Memory | 6 | Load, Store, GcAlloc |
| Collections | 7 | ArrayLit, DictLit, IndexGet |
| Closures | 2 | ClosureCreate, IndirectCall |
| Objects | 6 | StructInit, FieldGet, MethodCall |
| Patterns | 6 | PatternTest, PatternBind |
| Async | 5 | FutureCreate, Await, ActorSpawn |
| Generators | 3 | GeneratorCreate, Yield |
| Contracts | 2 | ContractCheck, ContractOldCapture |

## Stdlib Variant System

### Memory Model Matrix

| Directory | GC | Mutable |
|-----------|-----|---------|
| `core/` | Yes | Yes |
| `core_immut/` | Yes | No |
| `core_nogc/` | No | Yes |
| `core_nogc_immut/` | No | No |

### Host Variants (Default: `async_nogc_mut`)
```
host/
├── async_gc_mut/
├── async_gc_immut/
├── async_nogc_mut/   # DEFAULT
├── sync_nogc_mut/
└── common/
```

## Adding New Features

1. **Parser changes**: `src/parser/src/`
2. **Type system**: `src/type/src/`
3. **HIR lowering**: `src/compiler/src/hir/`
4. **MIR lowering**: `src/compiler/src/mir/`
5. **Codegen**: `src/compiler/src/codegen/`
6. **Runtime support**: `src/runtime/src/`
7. **Tests**: `src/driver/tests/`

## Architecture Rules

- `common` has no dependencies
- `parser` depends only on `common`
- `runtime` is independent of `compiler`
- `driver` is the only CLI entry point
- No circular dependencies between crates

## See Also

- `doc/architecture/README.md` - Full architecture docs
- `doc/codegen_technical.md` - Codegen details
- `doc/codegen/status.md` - MIR coverage
- `CLAUDE.md` - Current file structure
