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
- **DynTrait(String)**: Already exists! Dynamic trait object type
- **TypeScheme**: For let-polymorphism (∀vars. ty)
- **Substitution**: Type variable substitution
- **TraitImplRegistry**: Tracks blanket/specific impls with coherence checking

**Already exists:**
- `Type::DynTrait(String)` - dynamic trait object type

**Missing for static polymorphism:**
- `Type::StaticTrait(String)` - static trait type
- `Type::DispatchableTrait(String)` - compiler-chosen dispatch
- Interface binding mechanism (`BindingEnv`)

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

### 2.3 Existing Lean Generation System (`src/compiler/src/codegen/lean/`)

**The codebase already has comprehensive Lean4 code generation:**

| Module | Purpose |
|--------|---------|
| `mod.rs` | `LeanCodegen` - Main generator from HIR |
| `types.rs` | `TypeTranslator` - Simple → Lean type translation |
| `functions.rs` | `FunctionTranslator` - Function → Lean def |
| `contracts.rs` | `ContractTranslator` - Contracts → Lean theorems |
| `expressions.rs` | `ExprTranslator` - Expressions → Lean expressions |
| `emitter.rs` | `LeanEmitter` - Code writer |
| `runner.rs` | `LeanRunner` - Run Lean, check proofs |
| `verification_checker.rs` | Verification checking |

**CLI Integration** (`src/driver/src/cli/gen_lean.rs`):
```bash
simple gen-lean generate    # Generate Lean files to stdout
simple gen-lean compare     # Compare generated vs existing
simple gen-lean write       # Write generated files
```

**What exists:**
- Type translation (primitives, structs, enums → structure/inductive)
- Function translation (Simple → Lean def)
- Contract translation (requires/ensures → theorems)
- Lean runner for proof checking

**What needs to be added for static polymorphism:**
- Trait class generation (`class Logger (α : Type)`)
- Instance generation (`instance : Logger Console`)
- Binding generation (`abbrev Logger.Bound := Console`)
- Binding validity theorems

### 2.4 Module System

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

### 6.2 Lean4 Code Generator Module

**Location:** `src/compiler/src/lean_gen/` (new module)

```rust
// lean_gen/mod.rs
pub mod types;
pub mod traits;
pub mod bindings;
pub mod proofs;
pub mod writer;

use simple_parser::ast::{TraitDef, ImplBlock, ClassDef, BindStmt};

pub struct LeanGenerator {
    output_dir: PathBuf,
    project_name: String,
}

impl LeanGenerator {
    /// Generate Lean4 code from Simple AST
    pub fn generate(&self, modules: &[Module]) -> Result<(), LeanGenError> {
        // 1. Collect all traits, impls, classes, bindings
        let context = self.collect_definitions(modules)?;

        // 2. Generate type definitions
        self.generate_types(&context)?;

        // 3. Generate trait classes
        self.generate_traits(&context)?;

        // 4. Generate instances (implementations)
        self.generate_instances(&context)?;

        // 5. Generate binding constraints
        self.generate_bindings(&context)?;

        // 6. Generate proof obligations
        self.generate_proofs(&context)?;

        // 7. Generate lakefile.lean
        self.generate_lakefile()?;

        Ok(())
    }
}
```

### 6.3 Simple → Lean Translation Rules

| Simple Construct | Lean4 Generated Code |
|------------------|---------------------|
| `trait Logger` | `class Logger (α : Type) where` |
| `fn log(msg: Str)` (in trait) | `log : String → α → IO Unit` |
| `impl Logger for Console` | `instance : Logger Console where` |
| `class Point { x: Int, y: Int }` | `structure Point where x : Int; y : Int` |
| `bind Logger = Console` | `abbrev Logger.Bound := Console` |
| `dyn Logger` | `∃ α, Logger α × α` |
| `static Logger` | `Logger.Bound` |
| `x: Logger` (dispatchable) | `{α : Type} → [Logger α] → α` |

### 6.4 Example: Simple to Lean4 Translation

**Simple Source (`infra/log.spl`):**
```spl
trait Logger:
    fn log(msg: Str)
    fn level() -> Int

class ConsoleLogger impl Logger:
    fn log(msg: Str):
        print(msg)

    fn level() -> Int:
        return 1

class FileLogger impl Logger:
    path: Str

    fn log(msg: Str):
        file.append(self.path, msg)

    fn level() -> Int:
        return 2
```

**Generated Lean4 (`verification/generated/InfraLog.lean`):**
```lean
/-
  Auto-generated from infra/log.spl
  DO NOT EDIT - regenerate with: simple --gen-lean infra/log.spl
-/

-- Trait definition
class Logger (α : Type) where
  log : α → String → IO Unit
  level : α → Int

-- ConsoleLogger structure
structure ConsoleLogger where
  deriving Repr

-- ConsoleLogger implements Logger
instance : Logger ConsoleLogger where
  log _ msg := IO.println msg
  level _ := 1

-- FileLogger structure
structure FileLogger where
  path : String
  deriving Repr

-- FileLogger implements Logger
instance : Logger FileLogger where
  log self msg := IO.FS.appendFile self.path msg
  level _ := 2

-- Prove that both implementations are valid
theorem consoleLogger_valid : Logger ConsoleLogger := inferInstance
theorem fileLogger_valid : Logger FileLogger := inferInstance
```

**Simple Source (`app/__init__.spl`):**
```spl
mod app:
    bind Logger = ConsoleLogger
```

**Generated Lean4 (`verification/generated/AppBindings.lean`):**
```lean
/-
  Auto-generated from app/__init__.spl
  DO NOT EDIT
-/

import InfraLog

-- Interface binding: Logger is bound to ConsoleLogger
abbrev Logger.Bound := ConsoleLogger

-- The bound type satisfies the interface
instance Logger.BoundInstance : Logger Logger.Bound := inferInstance

-- Theorem: Using the binding is type-safe
theorem binding_sound : Logger Logger.Bound := Logger.BoundInstance

-- Theorem: Dispatch to bound type is deterministic
theorem binding_deterministic (x : Logger.Bound) (y : Logger.Bound) :
    Logger.log x = Logger.log y ∧ Logger.level x = Logger.level y := by
  simp [Logger.log, Logger.level]
```

### 6.5 Verification Properties (Auto-Generated)

The generator produces proofs for:
1. **Binding validity**: Bound type implements the interface
2. **Implementation completeness**: All trait methods are implemented
3. **Method signature match**: Impl method types match trait declaration
4. **Coherence**: No overlapping instances for the same type

### 6.6 Generator CLI Integration

```bash
# Generate Lean from a single file
simple --gen-lean src/infra/log.spl -o verification/generated/

# Generate Lean from entire project
simple --gen-lean . -o verification/generated/

# Generate and verify in one step
simple --verify src/  # Generates Lean, runs lake build, reports results

# CI integration
simple --verify --fail-on-unproven src/
```

### 6.7 Incremental Generation

```rust
// Track which Simple files have changed
pub struct LeanGenCache {
    file_hashes: HashMap<PathBuf, u64>,
    last_generated: HashMap<PathBuf, PathBuf>,  // .spl → .lean mapping
}

impl LeanGenCache {
    /// Only regenerate Lean for changed Simple files
    pub fn generate_incremental(&mut self, changed: &[PathBuf]) -> Result<(), Error> {
        for spl_file in changed {
            let lean_file = self.lean_path_for(spl_file);
            self.generate_single(spl_file, &lean_file)?;
            self.update_hash(spl_file)?;
        }
        Ok(())
    }
}

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
