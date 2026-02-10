# Architecture Skill - Simple Compiler

## Module Dependency Graph

```
cli (CLI entry) ──────────────────────────────┐
    │                                         │
    ├── compiler (HIR, MIR, Codegen) ─────────┤
    │       │                                 │
    │       ├── core (Lexer, Parser, AST) ────┤
    │       │                                 │
    │       └── std (Standard library) ───────┤
    │                                         │
    ├── app (Applications) ───────────────────┤
    │   ├── build (Build system)              │
    │   ├── mcp (MCP server)                  │
    │   ├── io (SFFI I/O)                     │
    │   └── test_runner (Test framework)      │
    │                                         │
    └── lib (Libraries) ──────────────────────┘
        └── database (SDN tables, atomic ops)
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

### Source Code (`src/`)
```
src/
├── app/         # Applications (100% Simple)
│   ├── build/   # Self-hosting build system
│   ├── cli/     # CLI entry point
│   ├── mcp/     # MCP server
│   ├── desugar/ # Static method desugaring
│   ├── fix/     # EasyFix auto-corrections
│   ├── lint/    # Linter
│   ├── io/      # I/O module (SFFI)
│   └── test_runner_new/ # Test runner + SDoctest
├── lib/         # Libraries
│   └── database/ # Database library (SDN tables, atomic ops)
├── std/         # Standard library
│   ├── spec.spl # SSpec BDD framework
│   ├── string.spl
│   ├── array.spl
│   ├── math.spl
│   ├── path.spl
│   └── platform/ # Cross-platform support
├── core/        # Core Simple library (self-hosting)
│   ├── tokens.spl
│   ├── types.spl
│   ├── ast.spl
│   ├── mir.spl
│   ├── lexer.spl
│   ├── parser.spl
│   └── error.spl
└── compiler/    # Compiler source (Simple)
    └── seed/      # Seed compiler (C/C++)
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

1. **Parser changes**: `src/core/parser.spl`, `src/core/lexer.spl`
2. **Type system**: `src/core/types.spl`
3. **HIR lowering**: `src/compiler/`
4. **MIR lowering**: `src/core/mir.spl`
5. **Standard library**: `src/std/`
6. **Applications/tools**: `src/app/`
7. **Tests**: `test/`

## Architecture Rules

- `src/core/` has no dependencies on other Simple modules
- `src/std/` depends only on `src/core/`
- `src/lib/` depends on `src/std/` and `src/core/`
- `src/app/cli/` is the only CLI entry point
- No circular dependencies between modules

---

## Lean 4 Verification

### Verification Projects

```
verification/
├── type_inference_compile/    # Type inference soundness
│   ├── TypeInferenceCompile.lean   # Core inference (determinism theorem)
│   ├── Generics.lean               # Generic type verification
│   ├── Contracts.lean              # Contract verification
│   ├── Traits.lean                 # Trait system
│   ├── Mixins.lean                 # Mixin composition
│   ├── StaticPolymorphism.lean     # Static dispatch
│   └── AsyncEffectInference.lean   # Effect inference
├── memory_capabilities/       # Reference capabilities (mut T, iso T)
├── memory_model_drf/          # SC-DRF memory model
├── manual_pointer_borrow/     # Borrow checker model
├── gc_manual_borrow/          # GC safety proofs
├── async_compile/             # Effect tracking
├── nogc_compile/              # NoGC instruction safety
├── module_resolution/         # Module path resolution
├── visibility_export/         # Export visibility rules
└── macro_auto_import/         # Macro import safety
```

### Lean Generation Commands

```bash
# Generate Lean files
simple gen-lean generate                    # All projects
simple gen-lean generate --project memory   # Specific project

# Compare generated vs existing
simple gen-lean compare                     # Show status
simple gen-lean compare --diff              # Show differences

# Write to verification/
simple gen-lean write --force               # Regenerate all

# Exit codes:
# 0 = identical, 1 = differences (safe to replace), 2 = missing definitions
```

### Type Inference Verification Impact

The `type_inference_compile` project proves:

1. **Determinism**: `theorem infer_deterministic` - inference yields at most one type
2. **Soundness**: Well-typed expressions don't get stuck
3. **Generics**: Type parameter substitution preserves typing
4. **Contracts**: Pre/postcondition contract verification

**When modifying type inference:**
1. Update `src/core/types.spl` (Simple implementation)
2. Update corresponding Lean theorems in `verification/type_inference_compile/`
3. Run `lake build` in verification project to check proofs
4. Run `simple gen-lean compare` to verify alignment

### Adding Verified Features

```simple
# Mark function for verification
@verify(memory)
fn safe_swap(a: mut ref Int, b: mut ref Int):
    """Swap with verified memory safety."""
    let temp = *a
    *a = *b
    *b = temp

@verify(types)
fn generic_map<T, U>(items: List<T>, f: fn(T) -> U) -> List<U>:
    """Generic function with verified type inference."""
    return [f(item) for item in items]
```

Generated Lean (in `verification/`):
```lean
def safe_swap (a b : MutRef Int) : Unit := do
  let temp ← a.read
  a.write (← b.read)
  b.write temp

theorem safe_swap_preserves_memory : ∀ a b,
  disjoint a b → valid_after (safe_swap a b) := by
  sorry  -- Proof stub
```

---

## Dependency Management

### Module Dependency Rules

| Layer | May Access | May Not Access |
|-------|------------|----------------|
| `src/app/cli/` | all | - |
| `src/compiler/` | core, std | app |
| `src/core/` | (no deps) | compiler, app |
| `src/std/` | core | compiler, app |
| `src/lib/` | std, core | compiler |

### Circular Dependency Prevention

**Before Design:**
1. Draw dependency graph of affected modules
2. Identify potential cycles

**After Implementation:**
1. Run `simple gen-lean compare` if verification-related
2. Verify no new circular imports

### Breaking Dependency Cycles

1. **Extract shared interface** → move to `src/core/`
2. **Invert dependency** → use trait/callback
3. **Split module** → separate concerns
4. **Use dependency injection** → runtime configuration

---

## Design Checklist

### Before Implementing

- [ ] Read relevant feature spec (`doc/feature/`)
- [ ] Identify affected modules and verification projects
- [ ] Draw dependency impact diagram

### After Implementing

- [ ] Run `bin/simple test` - all tests pass
- [ ] Run `simple gen-lean compare` - if verification affected
- [ ] Update Lean proofs if needed (`lake build`)

## See Also

- **`doc/guide/architecture_writing.md`** - Architecture writing guide (Skeleton→Verify→Diagram workflow)
- `doc/architecture/README.md` - Full architecture docs
- `doc/codegen_technical.md` - Codegen details
- `doc/codegen/status.md` - MIR coverage
- `doc/formal_verification.md` - Lean verification docs
- `verification/*/lakefile.lean` - Lean project configs
- `CLAUDE.md` - Current file structure
