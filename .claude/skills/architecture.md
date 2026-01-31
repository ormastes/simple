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
    │       ├── codegen/lean (Lean gen) ──────┤  ← Lean 4 verification
    │       │                                 │
    │       └── runtime (GC, Values) ─────────┤
    │               │                         │
    │               └── log ──────────────────┤
    │                                         │
    ├── loader (SMF binary loader) ───────────┤
    │                                         │
    ├── native_loader (OS dylib) ─────────────┤
    │                                         │
    ├── arch_test (Dependency analysis) ──────┤
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

### Lean Codegen Architecture

```
src/compiler/src/codegen/lean/
├── mod.rs              # LeanCodegen entry point
├── types.rs            # TypeTranslator (Simple→Lean types)
├── functions.rs        # FunctionTranslator
├── contracts.rs        # ContractTranslator (in:/out: → theorems)
├── expressions.rs      # ExprTranslator
├── traits.rs           # TraitTranslator (→ Lean type classes)
├── emitter.rs          # LeanEmitter (code generation)
├── runner.rs           # LeanRunner (proof checking)
├── verification_checker.rs
└── verification_diagnostics.rs
```

### Type Inference Verification Impact

The `type_inference_compile` project proves:

1. **Determinism**: `theorem infer_deterministic` - inference yields at most one type
2. **Soundness**: Well-typed expressions don't get stuck
3. **Generics**: Type parameter substitution preserves typing
4. **Contracts**: Pre/postcondition contract verification

**When modifying type inference:**
1. Update `src/type/src/lib.rs` (Rust implementation)
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
fn generic_map[T, U](items: List[T], f: fn(T) -> U) -> List[U]:
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

## Dependency Analysis

### arch_test Crate

Static analysis for enforcing architectural rules.

```rust
use arch_test::{Architecture, Layer};

let arch = Architecture::new()
    .layer("presentation", &["src/ui/**"])
    .layer("business", &["src/services/**"])
    .layer("data", &["src/repos/**"])
    .rule(Layer("presentation").may_only_access(&["business"]))
    .rule(Layer("business").may_not_access(&["presentation"]))
    .rule(Layer("data").may_not_be_accessed_by(&["presentation"]));

let result = arch.check("src/");
assert!(result.is_ok());
```

### Running Architecture Tests

```bash
make arch-test              # Run architecture tests
make arch-test-visualize    # Generate DOT/Mermaid graphs
```

### Circular Dependency Prevention

**Before Design:**
1. Draw dependency graph of affected modules
2. Identify potential cycles
3. Use `make arch-test` to validate current state

**After Implementation:**
1. Run `make arch-test` to verify no new cycles
2. Run `simple gen-lean compare` if verification-related
3. Check `cargo tree -p <crate>` for unexpected dependencies

### Dependency Rules by Layer

| Layer | May Access | May Not Access |
|-------|------------|----------------|
| `driver` | all | - |
| `compiler` | parser, type, runtime, common | driver |
| `parser` | common | compiler, runtime |
| `runtime` | log, common | compiler, parser |
| `common` | - | all |

### Detecting Cycles

```bash
# Rust crate cycles
cargo tree --edges features

# Simple module cycles (via arch_test)
make arch-test

# Lean project dependencies
cd verification/type_inference_compile && lake build
```

### Breaking Dependency Cycles

1. **Extract shared interface** → move to `common`
2. **Invert dependency** → use trait/callback
3. **Split module** → separate concerns
4. **Use dependency injection** → runtime configuration

---

## Design Checklist

### Before Implementing

- [ ] Read relevant feature spec (`doc/features/`)
- [ ] Check existing architecture (`make arch-test`)
- [ ] Identify affected verification projects
- [ ] Draw dependency impact diagram

### After Implementing

- [ ] Run `make arch-test` - no new violations
- [ ] Run `simple gen-lean compare` - if verification affected
- [ ] Run `cd rust && cargo test --workspace` - all tests pass
- [ ] Update Lean proofs if needed (`lake build`)

## See Also

- **`doc/guide/architecture_writing.md`** - Architecture writing guide (Skeleton→Verify→Diagram workflow)
- `doc/architecture/README.md` - Full architecture docs
- `doc/codegen_technical.md` - Codegen details
- `doc/codegen/status.md` - MIR coverage
- `doc/formal_verification.md` - Lean verification docs
- `verification/*/lakefile.lean` - Lean project configs
- `CLAUDE.md` - Current file structure
