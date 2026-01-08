# Static Polymorphism Research Document

**Date:** 2026-01-08
**Status:** Research Phase
**Related:** Type Inference, Module System, Lean4 Verification

## 1. Executive Summary

This document describes the design for **static polymorphism** (bindable interfaces) in the Simple language. The feature allows traits/interfaces to be compiled as either:
- **Dynamic dispatch** (vtable-based): One codepath, smaller binaries, faster compile
- **Static dispatch** (CRTP-like/monomorphized): Specialized code per implementor, larger binaries, best runtime

The key innovation is **package-root binding**: The `__init__.spl` file declares which implementation is bound to each interface, enabling compile-time specialization while maintaining a clean separation of concerns.

## 2. Current State Analysis

### 2.1 Type System (`src/type/src/lib.rs`)

The current type system has:
- **LeanTy/LeanExpr**: Types matching Lean4 verification model
- **lean_infer()**: Pure type inference function (verified in Lean4)
- **Full Type enum**: `Int`, `Bool`, `Str`, `Generic`, `Named`, `Function`, etc.

Missing for static polymorphism:
- No `dyn T` / `static T` type modifiers
- No trait bound resolution in type inference
- No interface binding mechanism

### 2.2 Trait System (Lean4 Models)

**`verification/type_inference_compile/src/Traits.lean`** models:
- `TraitDef`: Trait definition with methods and associated types
- `TraitImpl`: Implementation for a concrete type
- `inferTraitMethodCall`: Type inference for trait method calls
- `checkCoherence`: No overlapping implementations

**`verification/type_inference_compile/src/Classes.lean`** models:
- `ClassDef`: Class with fields, methods, type parameters
- `inferFieldAccess`, `inferMethodCall`: Type inference
- `isSubtype`: Inheritance checking

### 2.3 Module System

**`__init__.spl`** serves as package root manifest:
- `mod X` declarations for child modules
- `export use` for public API
- `common use` for directory prelude
- `requires [...]` for capability restrictions

This is the natural location for `bind` statements.

## 3. Design Specification

### 3.1 Syntax: `bind I = T`

```
bind_stmt ::= bind_prefix? "bind" dispatch_mode? trait_path "=" type_path
bind_prefix ::= "common" | "pub"
dispatch_mode ::= "static" | "dyn" | "auto"
```

**Examples:**
```spl
# __init__.spl (package root)
mod my_app:
    export use prelude.*

    # Interface bindings
    bind Logger = infra.log.ConsoleLogger
    bind Storage = infra.store.SqliteStorage

    # Explicit mode
    bind static Scheduler = concurrency.WorkStealingScheduler

    # Public binding (part of API surface)
    pub bind Crypto = infra.crypto.RingCrypto
```

### 3.2 Type Forms

| Type Form | Representation | Dispatch | When to Use |
|-----------|---------------|----------|-------------|
| `dyn I` | `{ data_ptr, vtbl_ptr }` | Always dynamic | Need runtime polymorphism |
| `static I` | Concrete type `T` | Always static | Performance-critical code |
| `I` (unqualified) | Compiler chooses | Dispatchable | Default, let compiler decide |

### 3.3 Semantic Rules

**Compile-time enforcement** when `bind I = T` is declared:

```spl
# Given: bind Logger = ConsoleLogger

let x: Logger = ConsoleLogger()    # OK - bound type
let y: Logger = FileLogger()       # ERROR - not the bound type
let z: dyn Logger = FileLogger()   # OK - explicit dynamic dispatch
```

**Resolution order for unqualified `I`:**
1. If `bind I = T` exists in package root: use static dispatch
2. If optimizer proves single implementor: devirtualize
3. Else: use dynamic dispatch

### 3.4 Build-Mode Overrides

```bash
--iface-dispatch=auto    # Default: use bindings + optimization
--iface-dispatch=dyn     # Force I → dynamic dispatch
--iface-dispatch=static  # Force I → static (error if ambiguous)
```

### 3.5 ABI Considerations

| Export Type | Requirement | Reason |
|-------------|-------------|--------|
| `pub fn(x: dyn I)` | Stable ABI | Dynamic representation fixed |
| `pub fn(x: static I)` | Monomorphized ABI | Caller knows concrete type |
| `pub fn(x: I)` | Internal only | May change between builds |

## 4. Lean4 Verification Model

### 4.1 New Lean Module: `InterfaceBinding.lean`

```lean
/-
  InterfaceBinding.lean - Formal verification of interface binding

  Models the static polymorphism feature with:
  - Binding declarations (bind I = T)
  - Dispatch mode selection
  - Type checking with bindings
-/

-- Dispatch mode
inductive DispatchMode where
  | dynamic    -- Always vtable
  | static_    -- Always monomorphized
  | auto       -- Compiler chooses
  deriving DecidableEq, Repr

-- Interface type with dispatch mode
inductive IfaceTy where
  | dyn (name : String)           -- dyn I
  | static_ (name : String)       -- static I
  | dispatchable (name : String)  -- I (unqualified)
  deriving Repr

-- Interface binding
structure InterfaceBinding where
  interface_name : String
  impl_type : Ty
  mode : DispatchMode
  deriving Repr

-- Binding environment (package root bindings)
def BindingEnv := List InterfaceBinding

-- Look up binding for an interface
def lookupBinding (env : BindingEnv) (ifaceName : String) : Option InterfaceBinding :=
  env.find? (fun b => b.interface_name == ifaceName)

-- Check if a type is valid for an interface given bindings
def checkIfaceType (bindings : BindingEnv) (registry : ImplRegistry)
    (ifaceTy : IfaceTy) (concreteTy : Ty) : Bool :=
  match ifaceTy with
  | IfaceTy.dyn name =>
      -- Any implementation is valid for dyn I
      implementsTrait registry concreteTy name
  | IfaceTy.static_ name =>
      match lookupBinding bindings name with
      | some binding => binding.impl_type == concreteTy
      | none => false  -- static requires binding
  | IfaceTy.dispatchable name =>
      match lookupBinding bindings name with
      | some binding => binding.impl_type == concreteTy
      | none => implementsTrait registry concreteTy name

-- Resolve dispatch mode for unqualified interface
def resolveDispatch (bindings : BindingEnv) (buildMode : DispatchMode)
    (ifaceName : String) : DispatchMode :=
  match buildMode with
  | DispatchMode.dynamic => DispatchMode.dynamic
  | DispatchMode.static_ => DispatchMode.static_
  | DispatchMode.auto =>
      match lookupBinding bindings ifaceName with
      | some binding => binding.mode
      | none => DispatchMode.dynamic

--==============================================================================
-- Theorems
--==============================================================================

-- Theorem: Binding lookup is deterministic
theorem binding_deterministic (env : BindingEnv) (name : String)
    (b1 b2 : InterfaceBinding) :
  lookupBinding env name = some b1 →
  lookupBinding env name = some b2 →
  b1 = b2 := by
  intro h1 h2
  simp [lookupBinding] at h1 h2
  sorry -- Proof depends on uniqueness of bindings

-- Theorem: Static dispatch requires binding
theorem static_requires_binding (bindings : BindingEnv) (registry : ImplRegistry)
    (name : String) (ty : Ty) :
  checkIfaceType bindings registry (IfaceTy.static_ name) ty = true →
  (lookupBinding bindings name).isSome := by
  intro h
  simp [checkIfaceType] at h
  split at h
  · simp
  · contradiction

-- Theorem: Dynamic dispatch is always more permissive
theorem dyn_more_permissive (bindings : BindingEnv) (registry : ImplRegistry)
    (name : String) (ty : Ty) :
  checkIfaceType bindings registry (IfaceTy.dispatchable name) ty = true →
  checkIfaceType bindings registry (IfaceTy.dyn name) ty = true := by
  intro h
  simp [checkIfaceType] at *
  sorry -- Proof follows from implementsTrait check

-- Theorem: No ambiguity with bindings
-- If a binding exists, dispatchable behaves like static
theorem binding_disambiguates (bindings : BindingEnv) (registry : ImplRegistry)
    (name : String) (ty : Ty) (binding : InterfaceBinding) :
  lookupBinding bindings name = some binding →
  checkIfaceType bindings registry (IfaceTy.dispatchable name) ty =
  checkIfaceType bindings registry (IfaceTy.static_ name) ty := by
  intro h
  simp [checkIfaceType, h]
```

### 4.2 Integration with Existing Models

The new model imports and extends:
- `Classes.lean`: `Ty`, `ClassDef`, type operations
- `Traits.lean`: `TraitDef`, `TraitImpl`, `ImplRegistry`, `implementsTrait`

## 5. Implementation Components

### 5.1 Parser (`src/parser/`)

**New AST nodes:**

```rust
// In ast/nodes/modules.rs
pub struct BindStmt {
    pub visibility: Visibility,      // pub, common, or private
    pub mode: DispatchMode,          // static, dyn, or auto
    pub interface_path: ModulePath,  // The trait/interface
    pub impl_path: ModulePath,       // The implementing type
    pub span: Span,
}

pub enum DispatchMode {
    Static,
    Dynamic,
    Auto,  // Default
}
```

**Token additions:**
- `Token::Bind` keyword

**Parser changes:**
- Add `parse_bind_stmt()` in `statements/mod.rs`
- Integrate into `parse_module_statement()`

### 5.2 Type Checker (`src/type/`)

**New functionality:**

```rust
// In checker_builtins.rs or new file checker_bindings.rs

pub struct BindingEnv {
    bindings: HashMap<String, InterfaceBinding>,
}

pub struct InterfaceBinding {
    pub interface_name: String,
    pub impl_type: Type,
    pub mode: DispatchMode,
}

impl BindingEnv {
    pub fn lookup(&self, interface: &str) -> Option<&InterfaceBinding>;

    pub fn check_iface_type(
        &self,
        iface_ty: &InterfaceType,
        concrete_ty: &Type,
        impl_registry: &ImplRegistry,
    ) -> Result<(), TypeError>;
}
```

### 5.3 HIR/MIR (`src/compiler/src/hir/`, `src/compiler/src/mir/`)

**HIR changes:**
- Add `HirIfaceType` with dispatch mode information
- Track binding context through lowering

**MIR changes:**
- Add `MirDispatchMode` annotation on method calls
- `MethodCall` instruction includes resolved dispatch info

### 5.4 Interpreter (`src/compiler/src/interpreter*.rs`)

**Changes in `interpreter_helpers/method_dispatch.rs`:**

```rust
pub fn dispatch_trait_method(
    receiver: Value,
    trait_name: &str,
    method_name: &str,
    args: &[Value],
    bindings: &BindingEnv,
    dispatch_mode: DispatchMode,
) -> Result<Value, CompileError> {
    match dispatch_mode {
        DispatchMode::Static => {
            // Must use bound implementation
            let binding = bindings.lookup(trait_name)
                .ok_or_else(|| CompileError::Semantic(
                    format!("static dispatch requires binding for {}", trait_name)
                ))?;
            dispatch_static(receiver, &binding.impl_type, method_name, args)
        }
        DispatchMode::Dynamic => {
            // Runtime dispatch via vtable
            dispatch_dynamic(receiver, trait_name, method_name, args)
        }
        DispatchMode::Auto => {
            // Check for binding, fall back to dynamic
            if let Some(binding) = bindings.lookup(trait_name) {
                dispatch_static(receiver, &binding.impl_type, method_name, args)
            } else {
                dispatch_dynamic(receiver, trait_name, method_name, args)
            }
        }
    }
}
```

### 5.5 Codegen (`src/compiler/src/codegen/`)

**Static dispatch (CRTP-like):**
```rust
// In codegen/instr/methods.rs
fn emit_static_dispatch(
    &mut self,
    receiver: Value,
    concrete_type: &Type,
    method: &str,
    args: &[Value],
) -> Value {
    // Direct call to concrete implementation
    let func_name = format!("{}::{}", concrete_type.name(), method);
    self.emit_direct_call(&func_name, std::iter::once(receiver).chain(args))
}
```

**Dynamic dispatch:**
```rust
fn emit_dynamic_dispatch(
    &mut self,
    receiver: Value,
    trait_name: &str,
    method: &str,
    args: &[Value],
) -> Value {
    // Load vtable pointer
    let vtable = self.emit_load_vtable(receiver);
    // Look up method in vtable
    let method_ptr = self.emit_vtable_lookup(vtable, trait_name, method);
    // Indirect call
    self.emit_indirect_call(method_ptr, std::iter::once(receiver).chain(args))
}
```

### 5.6 Module Resolver (`src/compiler/src/module_resolver/`)

**Changes in `manifest.rs`:**

```rust
pub struct DirectoryManifest {
    // ... existing fields ...
    pub bindings: Vec<BindingDecl>,  // NEW
}

pub struct BindingDecl {
    pub visibility: Visibility,
    pub mode: DispatchMode,
    pub interface_path: ModulePath,
    pub impl_path: ModulePath,
}

// In extract_manifest():
fn extract_manifest(module: &Module) -> DirectoryManifest {
    // ... existing code ...

    // Extract binding declarations
    let bindings = module.nodes.iter()
        .filter_map(|node| match node {
            Node::BindStmt(bind) => Some(BindingDecl::from(bind)),
            _ => None,
        })
        .collect();

    DirectoryManifest { /* ... */ bindings }
}
```

### 5.7 Linker (`src/compiler/src/linker/`)

**Symbol resolution with bindings:**

```rust
// In linker/analysis/symbol.rs
pub fn resolve_interface_symbol(
    &self,
    interface: &str,
    bindings: &BindingEnv,
) -> Option<Symbol> {
    if let Some(binding) = bindings.lookup(interface) {
        // Return the concrete type's symbol
        self.resolve_type_symbol(&binding.impl_type.to_string())
    } else {
        // No binding - must use dynamic dispatch
        self.resolve_vtable_symbol(interface)
    }
}
```

## 6. Simple → Lean4 Code Generation

### 6.1 Workflow

```
Simple Code (.spl)
       │
       ▼
   ┌─────────────────┐
   │     Parser      │
   └────────┬────────┘
            │
            ▼
   ┌─────────────────┐
   │ Lean4 Generator │───────────────────────────────────────┐
   │ (Rust module)   │                                       │
   └────────┬────────┘                                       │
            │                                                ▼
            │                                    ┌───────────────────────┐
            │                                    │  Generated Lean4 Code │
            │                                    │  (.lean files)        │
            │                                    └───────────┬───────────┘
            │                                                │
            │                                                ▼
            │                                    ┌───────────────────────┐
            │                                    │      lake build       │
            │                                    │  (type check proofs)  │
            │                                    └───────────┬───────────┘
            │                                                │
            │                                           ✓ or ✗
            │                                                │
            ▼                                                ▼
   ┌─────────────────┐                           ┌───────────────────────┐
   │  Type Checker   │ ◄─────────────────────────│ Verification Report   │
   │  (uses same     │                           │ (properties proven)   │
   │   inference)    │                           └───────────────────────┘
   └─────────────────┘
```

**Key Principle:** Lean code is GENERATED from Simple source, not hand-written.
The generator ensures that the Lean model exactly matches the Simple semantics.

### 6.2 Lean Generation Rules

| Simple Construct | Lean Equivalent |
|------------------|-----------------|
| `trait I` | `structure TraitDef` + `class I` |
| `impl I for T` | `instance : I T` |
| `bind I = T` | `abbrev I_Sel := T` + canonical instance |
| `dyn I` | `∃ t, I t` (existential) |
| `static I` | `I_Sel` (resolved alias) |
| `I` (dispatchable) | `I α` with `α` resolved at monomorphization |

### 6.3 Verification Properties

Generated Lean code should prove:
1. **Binding uniqueness**: Each interface has at most one binding per package
2. **Implementation completeness**: Bound type implements all trait methods
3. **Type safety**: `static I` values are always of the bound type
4. **Coherence**: No overlapping implementations after binding resolution

## 7. Component Interaction Flow

```
                    ┌──────────────────────────────────────────────────────────────┐
                    │                        __init__.spl                          │
                    │  bind Logger = ConsoleLogger                                 │
                    │  bind static Cache = RedisCache                              │
                    └──────────────────────────────────────────────────────────────┘
                                                │
                                                ▼
┌──────────────┐    ┌──────────────────────────────────────────────────────────────┐
│   Parser     │───▶│                    DirectoryManifest                         │
│              │    │  bindings: [{Logger→ConsoleLogger}, {Cache→RedisCache}]      │
└──────────────┘    └──────────────────────────────────────────────────────────────┘
                                                │
                    ┌───────────────────────────┼───────────────────────────┐
                    ▼                           ▼                           ▼
            ┌───────────────┐           ┌───────────────┐           ┌───────────────┐
            │  Type Checker │           │  Interpreter  │           │   Compiler    │
            │               │           │               │           │               │
            │ check_iface() │           │ dispatch()    │           │ emit_call()   │
            └───────────────┘           └───────────────┘           └───────────────┘
                    │                           │                           │
                    ▼                           ▼                           ▼
            ┌───────────────┐           ┌───────────────┐           ┌───────────────┐
            │ Type Error if │           │ Static or     │           │ Direct call   │
            │ wrong impl    │           │ Dynamic call  │           │ or vtable     │
            └───────────────┘           └───────────────┘           └───────────────┘
```

## 8. Test Strategy

### 8.1 Unit Tests

| Component | Test Cases |
|-----------|------------|
| Parser | Parse `bind` statements with all modifiers |
| Type Checker | Accept/reject implementations based on bindings |
| Interpreter | Static and dynamic dispatch correctness |
| Codegen | Generated code for both dispatch modes |

### 8.2 Integration Tests

```spl
# test_static_polymorphism.spl
trait Logger:
    fn log(msg: Str)

class ConsoleLogger impl Logger:
    fn log(msg: Str):
        print(msg)

class FileLogger impl Logger:
    fn log(msg: Str):
        file.write(msg)

# In __init__.spl:
# bind Logger = ConsoleLogger

fn test_binding():
    let logger: Logger = ConsoleLogger()  # OK
    # let bad: Logger = FileLogger()      # Should error
    let dyn_ok: dyn Logger = FileLogger() # OK with explicit dyn

# Run with: cargo test -p simple-driver static_polymorphism
```

### 8.3 Lean Verification Tests

```bash
cd verification/interface_binding
lake build  # Should succeed with all theorems proven
```

## 9. Migration Path

### Phase 1: Parser + AST (Foundation)
- Add `bind` keyword and AST node
- Parse `bind` statements in `__init__.spl`
- Extract bindings into `DirectoryManifest`

### Phase 2: Type Checking
- Create `BindingEnv` structure
- Implement `check_iface_type()` with binding awareness
- Add error messages for binding violations

### Phase 3: Lean Verification
- Create `InterfaceBinding.lean` module
- Prove core theorems
- Generate Lean from Simple trait definitions

### Phase 4: Interpreter Support
- Update method dispatch for static/dynamic modes
- Test with bound and unbound interfaces

### Phase 5: Compiler/Codegen
- HIR/MIR dispatch mode annotations
- Static dispatch code generation (direct calls)
- Dynamic dispatch code generation (vtables)

### Phase 6: Build System Integration
- `--iface-dispatch` compiler flag
- ABI stability checks for public APIs

## 10. Open Questions

1. **Binding inheritance**: Should child packages inherit parent bindings?
   - Proposal: Yes, with explicit override syntax

2. **Conditional bindings**: Should bindings depend on features/profiles?
   - Proposal: Defer to Phase 2

3. **Associated type bindings**: How do `bind` statements interact with associated types?
   - Proposal: Binding implicitly sets associated types from the impl

4. **Cross-package bindings**: Can library A provide bindings for library B's interfaces?
   - Proposal: No, bindings are package-local (applications can override)

## 11. References

- `doc/spec/traits.md` - Trait system specification
- `doc/import_export_and__init__.md` - Module system specification
- `verification/type_inference_compile/src/Traits.lean` - Trait Lean model
- `verification/type_inference_compile/src/Classes.lean` - Class Lean model
- User design document (provided in conversation)
