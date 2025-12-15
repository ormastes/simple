# Completed Features (Archive 1)

This document archives all completed features as of December 2025.

---

## Completed Infrastructure Components

| Component | Status | Notes |
|-----------|--------|-------|
| **Lexer** | ✅ Complete | Indentation-based, all tokens |
| **Parser** | ✅ Complete | Modular (expressions/statements/types) |
| **AST** | ✅ Complete | Full node coverage |
| **HIR** | ✅ Complete | Type-checked IR |
| **MIR** | ✅ Complete | 50+ instructions, generator lowering |
| **RuntimeValue** | ✅ Complete | 9 modules, 50+ FFI functions |
| **GC** | ✅ Complete | Abfall-backed with logging |
| **Package Manager** | ✅ Complete | UV-style with global cache |

---

## Completed Core Language Features

- **Basic Types** (i8-i64, u8-u64, f32-f64, bool, str, nil) ✅
- **Variables, Functions, Control Flow** ✅
- **Structs, Classes, Enums, Pattern Matching** ✅
- **GC Memory Management** ✅
- **Borrowing** ✅
- **Actors** ✅
- **Async/Await** ✅
- **Generators** ✅
- **Futures** ✅
- **Closures, Macros, String Interpolation** ✅

---

## Completed Codegen Features

- **Capture Buffer & VReg Remapping** ✅
- **Generator State Machine Codegen** ✅
- **LLVM Backend** ✅ (32-bit + 64-bit, 43 tests)

---

## Completed Testing Features

### BDD Spec Framework (from `doc/spec/bdd_spec.md`)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| TEST-001 | `describe` blocks | ✅ | Group related tests |
| TEST-002 | `context` blocks | ✅ | Nested context within describe |
| TEST-003 | `it` examples | ✅ | Individual test cases |
| TEST-004 | `before_each` hook | ✅ | Run before each example |
| TEST-005 | `after_each` hook | ✅ | Run after each example |
| TEST-006 | `before_all` hook | ✅ | Run once before all examples in group |
| TEST-007 | `after_all` hook | ✅ | Run once after all examples in group |
| TEST-008 | `expect ... to` matcher | ✅ | Value expectations |
| TEST-009 | `expect_raises` | ✅ | Block expectations for errors |

### Doctest (from `doc/spec/sdoctest.md`)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| DOC-001 | `>>>` prompt | ✅ | Doctest code block |
| DOC-002 | Expected output | ✅ | Lines after `>>>` |
| DOC-003 | `...` continuation | ✅ | Multi-line code |
| DOC-004 | `# doctest: +SKIP` | ✅ | Skip this example |
| DOC-005 | `# doctest: +ELLIPSIS` | ✅ | Match with `...` |
| DOC-006 | FFI integration | ✅ | Call compiled functions |

### Doctest Example

```simple
/// Adds two numbers.
///
/// >>> add(1, 2)
/// 3
///
/// >>> add(-1, 1)
/// 0
fn add(a: i64, b: i64) -> i64:
    return a + b
```

---

## Completed Formal Verification Features

Located in `verification/` directory, each project is a Lean 4 proof system.

### Type System Verification

| Feature ID | Project | Description | Status | Proven Theorems |
|------------|---------|-------------|--------|-----------------|
| FV-001 | `type_inference_compile` | Hindley-Milner type inference | ✅ | `infer_deterministic`, `emptySubst_identity` |
| FV-002 | `type_inference_compile/Generics` | Generic types with Algorithm W | ✅ | `unify_sound` (partial), `occurs_*` |

**Generics Model Details (FV-002):**
- Type variables (`Ty.var`)
- Generic types: `generic0`, `generic1`, `generic2` (up to 2 type params)
- Type schemes (`∀vars. ty`) for let-polymorphism
- Substitution with composition
- Unification with occurs check
- Instantiate/Generalize for let-bindings

### Memory Safety Verification

| Feature ID | Project | Description | Status | Notes |
|------------|---------|-------------|--------|-------|
| FV-010 | `manual_pointer_borrow` | Borrow checker model | ✅ | Matches Rust's borrow rules |
| FV-011 | `gc_manual_borrow` | GC safety model | ✅ | Proves GC root tracking |
| FV-012 | `nogc_compile` | NoGC instruction model | ✅ | Stack-only allocation proofs |

### Effect System Verification

| Feature ID | Project | Description | Status | Notes |
|------------|---------|-------------|--------|-------|
| FV-020 | `async_compile` | Async effect tracking | ✅ | Effect propagation, async safety |

### Module System Verification

| Feature ID | Project | Description | Status | Notes |
|------------|---------|-------------|--------|-------|
| FV-030 | `module_resolution` | Module resolution | ✅ | Import graph, cycle detection |
| FV-031 | `visibility_export` | Visibility rules | ✅ | Public/private export semantics |
| FV-032 | `macro_auto_import` | Macro auto-import | ✅ | Automatic macro visibility |

### Integration with Rust Implementation

The Rust type system in `src/type/` mirrors the Lean models:

| Lean Type | Rust Type | Location |
|-----------|-----------|----------|
| `Ty` | `Type` | `src/type/src/lib.rs` |
| `Scheme` | `TypeScheme` | `src/type/src/lib.rs` |
| `Subst` | `Substitution` | `src/type/src/lib.rs` |
| `unify` | `TypeChecker::unify` | `src/type/src/checker_unify.rs` |
| `instantiate` | `TypeChecker::instantiate` | `src/type/src/checker_builtins.rs` |
| `generalize` | `TypeChecker::generalize` | `src/type/src/checker_builtins.rs` |

### Building Verification Projects

```bash
cd verification/<project>
lake build
```

All projects use Lean 4 v4.26.0 (managed via `.elan`).

### Proven Theorems

- `infer_deterministic` - Type inference returns unique type
- `emptySubst_identity` - Empty substitution is identity
- `applySubst_*` - Substitution preserves primitives
- `occurs_*` - Occurs check properties

### Partial Proofs (with `sorry`)

- `unify_sound` - Unification produces correct substitution

---

## Completion Timeline (December 2025)

- ✅ LLVM Backend (32-bit + 64-bit, 43 tests)
- ✅ Generator State Machine Codegen
- ✅ Capture Buffer & VReg Remapping
- ✅ BDD Spec Framework Sprint 1
- ✅ Doctest Sprint 2
- ✅ JJ Integration (8/12 tasks - 67%)
- ✅ Generic Type Inference Model (Lean 4)
