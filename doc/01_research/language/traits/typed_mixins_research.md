# Typed Mixins Research

**Date:** 2026-01-08  
**Status:** Research & Planning Phase  
**Related:** Type System Enhancement, Lean Verification

## Overview

This document researches strongly-typed mixins for the Simple language with type inference support and formal verification via Lean 4.

## Goals

1. **Strong Typing:** Mixins with full type checking and inference
2. **Type Parameters:** Generic mixins with type parameter inference
3. **Trait Requirements:** Mixins can require traits on the target type
4. **Composability:** Multiple mixins can be applied with conflict resolution
5. **Formal Verification:** Generate Lean 4 proofs for type soundness

## Type System Requirements

### Type Inference Intensive Features

Mixins require advanced type inference for:

1. **Type Parameter Inference:** Infer generic type arguments from usage context
2. **Trait Constraint Resolution:** Automatically check trait bounds
3. **Field Type Unification:** Merge field types from multiple mixins
4. **Method Signature Matching:** Match required methods with implementations

### Example Type Inference Scenarios

```simple
# Scenario 1: Infer type parameter from field usage
mixin Cache<T>:
    var cache: HashMap<String, T>
    
    fn get_cached(key: String) -> Option<T>
    fn set_cache(key: String, value: T)

class UserService:
    use Cache  # T is inferred as User from context
    
    fn get_user(id: i64) -> User:
        if let Some(user) = self.get_cached(id.to_string()):
            return user  # Type checker infers T = User here
        # ...

# Scenario 2: Multiple type parameters
mixin Repository<T, E>:
    required fn connection() -> DbConnection
    
    fn find_by_id(id: i64) -> Result<T, E>:
        # Implementation uses E for error type

# Scenario 3: Trait requirements with inference
mixin Serializable where Self: Serialize + Deserialize:
    fn to_json() -> String
    fn from_json(json: String) -> Result<Self, Error>
```

## Grammar Design (LL(1) Compatible)

### Mixin Declaration

```ebnf
MixinDeclaration ::= 
    'mixin' IDENTIFIER TypeParams? WhereClause? ':' NEWLINE INDENT
        MixinBody
    DEDENT

TypeParams ::= '<' TypeParam (',' TypeParam)* '>'
TypeParam ::= IDENTIFIER (':' TypeBound)?
TypeBound ::= IDENTIFIER ('+' IDENTIFIER)*

WhereClause ::= 'where' WhereClausePredicate (',' WhereClausePredicate)*
WhereClausePredicate ::= 
    | 'Self' ':' TypeBound              # Trait requirement on target
    | TypeParam ':' TypeBound           # Trait requirement on type param
    
MixinBody ::=
    | MixinField
    | MixinMethod
    | MixinRequiredMethod

MixinField ::= 'var' IDENTIFIER ':' Type NEWLINE
MixinMethod ::= FunctionDeclaration
MixinRequiredMethod ::= 'required' 'fn' MethodSignature NEWLINE

MethodSignature ::= IDENTIFIER '(' ParamList? ')' ('->' Type)?
```

### Mixin Application

```ebnf
MixinApplication ::= 'use' MixinRef (',' MixinRef)* NEWLINE

MixinRef ::= 
    IDENTIFIER TypeArgs? MixinOptions?
    
TypeArgs ::= '<' Type (',' Type)* '>'

MixinOptions ::= 
    | 'with' MixinOverrides
    
MixinOverrides ::= '{' NEWLINE INDENT
    (FieldOverride | MethodOverride)*
    DEDENT '}'
    
FieldOverride ::= IDENTIFIER ':' Type NEWLINE
MethodOverride ::= FunctionDeclaration
```

### LL(1) Properties

- **Distinct Lookahead:** `mixin` keyword for declaration, `use` for application
- **No Ambiguity:** Type parameters use `<>`, trait bounds use `:`
- **Clear Scoping:** Indentation-based blocks (like Python)
- **Sequential Parsing:** All constructs can be parsed left-to-right

## Type Inference Algorithm

### Phase 1: Mixin Registration

1. Parse mixin declaration
2. Register mixin type with type parameters in environment
3. Store trait requirements and required methods

### Phase 2: Constraint Generation

For each `use Mixin<?>` application:

1. Create type variables for unknown type arguments
2. Generate constraints from:
   - Field usage context
   - Method call signatures  
   - Trait requirements
   - Required method implementations

### Phase 3: Constraint Solving

1. Unify type variables using Hindley-Milner algorithm
2. Check trait bounds are satisfied
3. Verify required methods are implemented
4. Resolve field/method conflicts

### Phase 4: Type Substitution

1. Apply solved type substitutions to mixin
2. Generate final class/struct type with merged fields/methods
3. Update type environment

## Lean Verification Strategy

### Generated Lean Artifacts

For each mixin, generate:

1. **Structure Definition:** Lean structure representing mixin fields
2. **Type Class:** For trait requirements
3. **Application Function:** Function that applies mixin to target type
4. **Theorems:**
   - Type soundness: Applied mixin preserves target type
   - Coherence: No duplicate mixin applications
   - Completeness: All required methods satisfied

### Example Generated Lean Code

```lean
-- From: mixin Cache<T>
structure Cache (T : Type) where
  cache : HashMap String T
  get_cached : String → Option T
  set_cache : String → T → Unit
deriving Repr

-- Application theorem
theorem apply_cache_preserves_type (C : Type) (c : C) (T : Type) :
  ∃ c' : C, c'.cache.valType = T → c = c'

-- Coherence theorem
theorem cache_no_duplicate (mixins : List MixinRef) :
  checkMixinCoherence mixins = true →
  ∀ m1 m2, m1 ∈ mixins → m2 ∈ mixins → 
    m1.name = "Cache" → m2.name = "Cache" → m1 = m2
```

## Implementation Phases

### Phase 0: BDD Specifications (Test-First)

Create Cucumber/Gherkin feature files:
- `specs/features/mixin_basic.feature` - Basic mixin declaration
- `specs/features/mixin_generic.feature` - Generic type parameters
- `specs/features/mixin_traits.feature` - Trait requirements
- `specs/features/mixin_composition.feature` - Multiple mixins

### Phase 1: Parser (10%)

1. Add `Mixin` keyword to lexer
2. Implement `parse_mixin_declaration()`
3. Implement `parse_mixin_application()`
4. Add AST nodes: `MixinDecl`, `MixinRef`

### Phase 2: Type System (40%)

1. Add `MixinType` to type registry
2. Implement mixin type inference
3. Add constraint generation for mixins
4. Implement mixin application with type checking

### Phase 3: HIR Lowering (20%)

1. Lower mixin declarations to HIR
2. Expand mixin applications to field/method additions
3. Generate vtables for mixin methods

### Phase 4: Lean Code Generation (20%)

1. Extend `LeanType::Mixin` emission
2. Generate mixin application functions
3. Generate type soundness theorems
4. Update verification test suite

### Phase 5: Testing & Documentation (10%)

1. Run BDD tests
2. Add integration tests
3. Update Lean verification proofs
4. Generate documentation from specs

## References

- Scala Traits: Mixin composition with linearization
- Rust Traits: Trait bounds and associated types
- TypeScript Mixins: Intersection types for composition
- Lean 4 Type Classes: Formal verification of type systems

## Next Steps

1. ✅ Create this research document
2. ⏭️ Write BDD feature specs (test-first)
3. ⏭️ Implement parser changes
4. ⏭️ Implement type inference for mixins
5. ⏭️ Generate Lean verification code
6. ⏭️ Test with Lean theorem prover

---

**Note:** This is a research document. Implementation should follow test-driven development with BDD specs written first.
