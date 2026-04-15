# Static Polymorphism Implementation Review

**Date:** 2026-01-08  
**Status:** Implementation Assessment  
**Related:** Mixin System, Type Inference, Lean Verification

## Executive Summary

This document reviews the current implementation status of **static polymorphism** (via mixins) and the **bind** statement system for compile-time dispatch. It identifies gaps, improvement opportunities, and provides a roadmap for completion.

## 1. Current Implementation Status

### 1.1 What Exists

#### Parser Support (✅ Mostly Complete)
- **Mixin keyword**: `Token::Mixin` in lexer
- **Mixin AST node**: `MixinDecl` in `ast/nodes/definitions.rs`
- **Use clause**: `use MixinName` within class/struct bodies
- **Parser methods**: `parse_mixin()` in `parser_impl/definitions.rs`

**Evidence:**
```rust
// src/parser/src/ast/nodes/definitions.rs
pub struct MixinDecl {
    pub name: String,
    pub type_params: Vec<GenericParam>,
    pub fields: Vec<FieldDecl>,
    pub methods: Vec<FunctionDecl>,
    pub required_methods: Vec<FunctionSignature>,
    pub span: Span,
}
```

#### Type Checking (✅ Partially Complete)
- **Mixin type checker**: `src/type/src/mixin_checker.rs`
- **Field conflict detection**: `check_mixin_field_conflicts()`
- **Field combination**: `combine_mixin_fields()`
- **Mixin application**: `apply_mixin_to_type()`

#### BDD Specifications (✅ Complete)
- `specs/features/mixin_basic.feature` - 10 scenarios
- `specs/features/mixin_generic.feature` - 15 scenarios
- Well-structured, covers edge cases

### 1.2 What's Missing

#### ❌ Bind Statement (CRITICAL)
The **core feature** of static polymorphism is missing:

```spl
bind Logger = ConsoleLogger
bind static Cache = RedisCache
pub bind Crypto = RingCrypto
```

**Missing components:**
1. `Token::Bind` keyword in lexer
2. `BindStmt` AST node
3. `parse_bind_stmt()` parser method
4. `BindingEnv` type checking infrastructure
5. Module manifest integration

#### ❌ Static Polymorphism Feature Specs
No BDD specs for:
- `bind` statement syntax
- Static vs dynamic dispatch selection
- Binding visibility (`pub bind`, `common bind`)
- Type inference with bindings
- Binding conflict resolution

#### ❌ Lean Verification for Bindings
Missing Lean4 model for:
- Interface binding semantics
- Dispatch mode selection
- Static dispatch soundness proofs

#### ❌ HIR/MIR Lowering
No HIR/MIR representation for:
- Dispatch mode annotations
- Binding-aware method calls
- Static vs dynamic call differentiation

#### ❌ Codegen Integration
No code generation for:
- Static dispatch (direct calls)
- Dynamic dispatch (vtables)
- Binding resolution at compile time

## 2. Implementation Gaps Analysis

### 2.1 Parser Gap: Bind Statement

**Priority:** HIGH  
**Complexity:** LOW  
**Estimated Effort:** 2-4 hours

**Required changes:**

```rust
// 1. Add token (src/parser/src/token.rs)
pub enum Token {
    // ... existing tokens ...
    Bind,  // NEW
}

// 2. Add AST node (src/parser/src/ast/nodes/modules.rs)
pub struct BindStmt {
    pub visibility: Visibility,      // pub, common, private
    pub mode: DispatchMode,          // static, dyn, auto
    pub interface_path: ModulePath,  
    pub impl_path: ModulePath,       
    pub span: Span,
}

pub enum DispatchMode {
    Static,   // static Logger = ...
    Dynamic,  // dyn Logger = ...
    Auto,     // Logger = ... (default)
}

// 3. Add parser (src/parser/src/parser_impl/statements.rs)
fn parse_bind_stmt(&mut self) -> Result<BindStmt, ParseError> {
    // bind [static|dyn] TraitPath = TypePath
    self.expect(Token::Bind)?;
    
    let mode = match self.peek() {
        Token::Static => { self.advance(); DispatchMode::Static },
        Token::Dyn => { self.advance(); DispatchMode::Dynamic },
        _ => DispatchMode::Auto,
    };
    
    let interface_path = self.parse_module_path()?;
    self.expect(Token::Assign)?;
    let impl_path = self.parse_module_path()?;
    
    Ok(BindStmt { mode, interface_path, impl_path, .. })
}
```

### 2.2 Type Checking Gap: BindingEnv

**Priority:** HIGH  
**Complexity:** MEDIUM  
**Estimated Effort:** 6-8 hours

**Required infrastructure:**

```rust
// src/type/src/binding_env.rs (NEW FILE)

/// Environment tracking interface bindings for static dispatch
pub struct BindingEnv {
    bindings: HashMap<String, InterfaceBinding>,
}

pub struct InterfaceBinding {
    pub interface_name: String,
    pub impl_type: Type,
    pub mode: DispatchMode,
    pub visibility: Visibility,
}

impl BindingEnv {
    /// Look up binding for an interface
    pub fn lookup(&self, interface: &str) -> Option<&InterfaceBinding>;
    
    /// Check if concrete type is valid for interface given bindings
    pub fn check_iface_type(
        &self,
        iface_ty: &InterfaceType,
        concrete_ty: &Type,
        impl_registry: &ImplRegistry,
    ) -> Result<(), TypeError>;
    
    /// Resolve dispatch mode for unqualified interface
    pub fn resolve_dispatch(
        &self,
        iface_name: &str,
        build_mode: DispatchMode,
    ) -> DispatchMode;
}
```

**Integration points:**
- `TypeChecker` needs `BindingEnv` field
- Method calls check bindings before dispatch
- Type inference uses bindings to specialize generic types

### 2.3 BDD Specification Gap

**Priority:** HIGH  
**Complexity:** LOW  
**Estimated Effort:** 4-6 hours

**Required specs:**

1. **`specs/features/static_polymorphism_bind.feature`**
   - Bind statement parsing
   - Visibility modifiers (pub bind, common bind)
   - Dispatch mode selection (static/dyn/auto)
   - Multiple bindings in same module

2. **`specs/features/static_polymorphism_dispatch.feature`**
   - Static dispatch with binding
   - Dynamic dispatch without binding
   - Auto dispatch selection
   - Type checking with bindings

3. **`specs/features/static_polymorphism_inference.feature`**
   - Type inference with bound interfaces
   - Generic type specialization
   - Conflict resolution

### 2.4 Lean Verification Gap

**Priority:** MEDIUM  
**Complexity:** HIGH  
**Estimated Effort:** 12-16 hours

**Required Lean modules:**

```lean
-- verification/type_inference_compile/src/InterfaceBinding.lean

inductive DispatchMode where
  | dynamic | static_ | auto

inductive IfaceTy where
  | dyn (name : String)
  | static_ (name : String)
  | dispatchable (name : String)

structure InterfaceBinding where
  interface_name : String
  impl_type : Ty
  mode : DispatchMode

def BindingEnv := List InterfaceBinding

def checkIfaceType (bindings : BindingEnv) (registry : ImplRegistry)
    (ifaceTy : IfaceTy) (concreteTy : Ty) : Bool := ...

theorem binding_deterministic : ... := by sorry
theorem static_requires_binding : ... := by sorry
theorem dyn_more_permissive : ... := by sorry
```

**Integration:**
- Extend existing `Traits.lean` model
- Add binding checks to `inferTraitMethodCall`
- Generate Lean from Simple bind statements

### 2.5 HIR/MIR Lowering Gap

**Priority:** MEDIUM  
**Complexity:** MEDIUM  
**Estimated Effort:** 8-10 hours

**Required changes:**

```rust
// src/compiler/src/hir/types/type_system.rs
pub enum HirType {
    // ... existing variants ...
    BoundInterface {
        name: String,
        concrete_type: Box<HirType>,
        mode: DispatchMode,
    },
}

// src/compiler/src/mir/instructions.rs
pub enum MirInstr {
    // ... existing variants ...
    MethodCall {
        receiver: MirValue,
        method: String,
        args: Vec<MirValue>,
        dispatch: DispatchInfo,  // NEW
    },
}

pub enum DispatchInfo {
    Static { impl_type: String },
    Dynamic { vtable: VTableId },
}
```

### 2.6 Codegen Gap

**Priority:** LOW (Interpreter first, codegen later)  
**Complexity:** HIGH  
**Estimated Effort:** 16-20 hours

**Required:**
- Static dispatch: direct function calls
- Dynamic dispatch: vtable lookups
- Binding resolution during codegen

## 3. Improvement Opportunities

### 3.1 Mixin Type Inference Enhancement

**Current:** Mixins require explicit type arguments  
**Improvement:** Infer type parameters from usage context

```spl
mixin Cache<T>:
    var cache: HashMap<String, T>
    fn get(key: String) -> Option<T>

class UserService:
    use Cache  # Infer T from usage, not explicit Cache<User>
    
    fn get_user(id: i64) -> Option<User>:
        return self.get(id.to_string())  # Infer T = User here
```

**Implementation:**
- Constraint-based type inference
- Unification of mixin type params with usage sites
- Error messages when inference fails

### 3.2 Mixin Composition Ordering

**Current:** Mixin application order not specified  
**Improvement:** Define deterministic composition rules

```spl
mixin A:
    fn foo(): print("A")

mixin B:
    fn foo(): print("B")

class C:
    use A, B  # Which foo() is used? Error or B.foo()?
```

**Options:**
1. **Error on conflict** (safest)
2. **Last wins** (B.foo() overrides A.foo())
3. **Explicit override syntax**

**Recommendation:** Error on conflict, require explicit resolution

### 3.3 Required Method Verification

**Current:** `required fn` in mixins not verified at compile time  
**Improvement:** Type checker ensures implementation

```spl
mixin Repository:
    required fn table_name() -> String

class UserRepo:
    use Repository
    # ERROR: Must implement table_name()
```

**Implementation:**
- Track required methods in MixinInfo
- Check implementing type provides all required methods
- Generate helpful error messages

### 3.4 Lean Code Generation Automation

**Current:** No automated Lean generation for mixins/bindings  
**Improvement:** `simple gen-lean` generates Lean models

```bash
simple gen-lean src/ -o verification/generated/
```

**Generated Lean:**
- Mixin definitions → Lean classes
- Bind statements → Lean abbreviations
- Required methods → Lean type class constraints
- Proofs of soundness

### 3.5 Documentation Generation from Specs

**Current:** BDD specs exist but don't generate docs  
**Improvement:** Auto-generate markdown from feature files

```bash
simple spec-doc specs/features/mixin_*.feature -o doc/features/mixins.md
```

**Output format:**
- Scenario descriptions
- Code examples
- Expected behavior
- Cross-references

## 4. Priority Roadmap

### Phase 1: Core Bind Statement (Week 1)
1. ✅ Add `Token::Bind` to lexer
2. ✅ Add `BindStmt` AST node
3. ✅ Implement `parse_bind_stmt()`
4. ✅ Add `bind` to module statement parsing
5. ✅ Create BDD specs for bind syntax

### Phase 2: Type Checking with Bindings (Week 2)
1. ✅ Create `binding_env.rs` module
2. ✅ Implement `BindingEnv` and `InterfaceBinding`
3. ✅ Integrate with `TypeChecker`
4. ✅ Add binding-aware type checking
5. ✅ Create BDD specs for dispatch selection

### Phase 3: Lean Verification (Week 3)
1. ✅ Create `InterfaceBinding.lean` module
2. ✅ Define dispatch mode ADT
3. ✅ Implement binding lookup and checking
4. ✅ Prove core theorems
5. ✅ Integrate with existing trait model

### Phase 4: HIR/MIR Lowering (Week 4)
1. ✅ Add dispatch annotations to HIR
2. ✅ Lower bind statements to HIR
3. ✅ Add dispatch info to MIR instructions
4. ✅ Test with interpreter

### Phase 5: Interpreter Integration (Week 5)
1. ✅ Update method dispatch logic
2. ✅ Implement static dispatch paths
3. ✅ Implement dynamic dispatch paths
4. ✅ Test with BDD scenarios

### Phase 6: Documentation & Polish (Week 6)
1. ✅ Generate docs from BDD specs
2. ✅ Update language manual
3. ✅ Add examples to `examples/`
4. ✅ Run full test suite

## 5. Testing Strategy

### 5.1 Unit Tests
- Parser: bind statement variants
- Type checker: binding lookup, conflict detection
- Lean: theorem proofs

### 5.2 Integration Tests
- Full compilation with bindings
- Interpreter execution
- Error messages

### 5.3 BDD Scenarios (Spec-First)
- Write scenarios BEFORE implementation
- Each scenario generates documentation
- Automated acceptance testing

### 5.4 Example Programs
- `examples/static_polymorphism.spl` (already exists)
- `examples/mixin_composition.spl` (NEW)
- `examples/bind_modes.spl` (NEW)

## 6. Open Issues

### 6.1 Binding Scope
**Question:** Should bindings be inherited by child modules?

```spl
# parent/__init__.spl
bind Logger = ConsoleLogger

# parent/child/__init__.spl
# Does Logger binding apply here? YES or NO?
```

**Options:**
1. **Inherit by default** (implicit)
2. **Explicit opt-in** (`use parent.bindings`)
3. **No inheritance** (each module binds independently)

**Recommendation:** Option 1 (inherit), allow override

### 6.2 Cross-Package Bindings
**Question:** Can library A bind library B's interfaces?

**Recommendation:** No. Bindings are package-local. Applications make final binding decisions.

### 6.3 Conditional Bindings
**Question:** Should bindings vary by build profile?

```spl
#[cfg(debug)]
bind Logger = VerboseLogger

#[cfg(release)]
bind Logger = FastLogger
```

**Recommendation:** Defer to future feature. Use build-time selection for now.

## 7. Verification Alignment

### 7.1 Lean Model Completeness
- ✅ Basic type system modeled
- ✅ Trait system modeled
- ❌ Mixin composition not modeled
- ❌ Binding semantics not modeled

### 7.2 Required Lean Updates
1. Add `Mixin` inductive type
2. Add `MixinApplication` composition rules
3. Add `InterfaceBinding` with dispatch modes
4. Prove binding soundness theorems

### 7.3 Auto-Generation
Implement `LeanMixinGenerator`:
- Converts `MixinDecl` → Lean class
- Converts `BindStmt` → Lean abbreviation
- Generates proof obligations

## 8. Recommendations

### 8.1 Immediate Actions (This Week)
1. **Create bind statement BDD specs** (4 hours)
2. **Implement bind parsing** (4 hours)
3. **Start binding_env.rs module** (6 hours)

### 8.2 Short-Term (Next 2 Weeks)
1. Complete type checking integration
2. Write Lean verification model
3. Update HIR lowering

### 8.3 Long-Term (Next Month)
1. Full interpreter support
2. Codegen for native backends
3. Documentation generation pipeline

## 9. Success Criteria

Implementation is **complete** when:
- ✅ All BDD scenarios pass
- ✅ Lean proofs verify
- ✅ Examples compile and run
- ✅ Documentation generated from specs
- ✅ No regressions in existing tests

## 10. Conclusion

**Status: ~40% Complete**

**Strong foundation exists:**
- Mixin parsing works
- Type checking infrastructure present
- BDD specs comprehensive

**Critical gaps:**
- Bind statement (high priority, low complexity)
- BindingEnv type checking (high priority, medium complexity)
- Lean verification (medium priority, high complexity)

**Recommended next step:** Implement bind statement parsing and create BDD specs. This unblocks subsequent phases.
