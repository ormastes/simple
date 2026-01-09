# Phase 2: Mixin Type System Implementation Plan

**Status:** Ready to begin  
**Estimated Time:** 40 hours (2 weeks)  
**Prerequisites:** ✅ Phase 1 complete (parser working)

## Overview

Implement type checking and inference for mixin composition, including:
- Mixin type representation
- Type substitution for generic mixins
- Composition validation
- Conflict detection
- Field/method resolution

## Architecture

### Type Representation

Mixins will use existing `Type::Named(String)` infrastructure, similar to classes:

```rust
// In Type enum (already exists)
Type::Named("SomeMixin")

// Mixin-specific metadata stored in:
struct MixinInfo {
    name: String,
    type_params: Vec<String>,
    fields: Vec<(String, Type)>,
    methods: Vec<(String, FunctionType)>,
    required_traits: Vec<String>,
    required_methods: Vec<RequiredMethodSig>,
}

// Type checker environment extension
struct TypeChecker {
    // ... existing fields ...
    mixins: HashMap<String, MixinInfo>,  // NEW
    compositions: HashMap<String, Vec<MixinRef>>,  // NEW: type -> mixins
}
```

## Implementation Steps

### Step 1: Mixin Registration (2 hours)

**File:** `src/type/src/checker_check.rs`

**Task:** Register mixin definitions in type environment

```rust
// In check_items(), handle Node::Mixin
Node::Mixin(mixin) => {
    // 1. Register mixin name
    let ty = self.fresh_var();
    self.env.insert(mixin.name.clone(), ty);
    
    // 2. Store mixin metadata
    let info = MixinInfo {
        name: mixin.name.clone(),
        type_params: mixin.generic_params.clone(),
        fields: mixin.fields.iter().map(|f| {
            (f.name.clone(), self.convert_ast_type(&f.ty))
        }).collect(),
        methods: /* ... */,
        required_traits: mixin.required_traits.clone(),
        required_methods: /* ... */,
    };
    self.mixins.insert(mixin.name.clone(), info);
    
    // 3. Check mixin body
    for field in &mixin.fields {
        self.check_field_type(&field.ty)?;
    }
    for method in &mixin.methods {
        self.check_function(method)?;
    }
}
```

**Tests:** 3 tests
- Register simple mixin
- Register generic mixin  
- Register mixin with methods

### Step 2: Type Substitution (4 hours)

**File:** `src/type/src/lib.rs`

**Task:** Implement generic mixin instantiation

```rust
impl Type {
    /// Substitute type parameters with concrete types
    pub fn substitute(&self, subst: &HashMap<String, Type>) -> Type {
        match self {
            Type::TypeParam(name) => subst.get(name).cloned().unwrap_or(self.clone()),
            Type::Generic { name, args } => {
                Type::Generic {
                    name: name.clone(),
                    args: args.iter().map(|a| a.substitute(subst)).collect(),
                }
            }
            Type::Named(name) => /* Check if name is type param */ self.clone(),
            /* ... other cases ... */
        }
    }
}

// Instantiate mixin with type arguments
fn instantiate_mixin(
    mixin: &MixinInfo,
    type_args: &[Type],
    self_ty: Type,
) -> Result<MixinInfo, TypeError> {
    // Build substitution map
    let mut subst = HashMap::new();
    for (param, arg) in mixin.type_params.iter().zip(type_args) {
        subst.insert(param.clone(), arg.clone());
    }
    subst.insert("Self".to_string(), self_ty);
    
    // Apply substitution to fields and methods
    Ok(MixinInfo {
        name: mixin.name.clone(),
        type_params: vec![],
        fields: mixin.fields.iter().map(|(name, ty)| {
            (name.clone(), ty.substitute(&subst))
        }).collect(),
        methods: /* ... */,
        /* ... */
    })
}
```

**Tests:** 5 tests
- Substitute simple type param
- Substitute nested generic
- Substitute in function type
- Instantiate mixin with Self
- Instantiate generic mixin Container[T] with T=i64

### Step 3: Composition Registration (3 hours)

**File:** `src/type/src/checker_check.rs`

**Task:** Register mixin compositions on classes/structs

```rust
// In Node::Class handler
Node::Class(class) => {
    // ... existing code ...
    
    // NEW: Register mixin compositions
    if !class.mixins.is_empty() {
        self.compositions.insert(
            class.name.clone(),
            class.mixins.clone()
        );
    }
}

// Similarly for Node::Struct
```

**Tests:** 2 tests
- Register class with single mixin
- Register struct with multiple mixins

### Step 4: Field Collection (5 hours)

**File:** `src/type/src/checker_check.rs`

**Task:** Collect all fields from composed mixins

```rust
fn collect_composed_fields(
    &self,
    type_name: &str,
) -> Result<Vec<(String, Type)>, TypeError> {
    let mut fields = Vec::new();
    let mut seen = HashSet::new();
    
    // Get mixin compositions
    if let Some(mixins) = self.compositions.get(type_name) {
        for mixin_ref in mixins {
            // Get mixin info
            let mixin_info = self.mixins.get(&mixin_ref.name)
                .ok_or_else(|| TypeError::UnknownMixin(mixin_ref.name.clone()))?;
            
            // Instantiate with type arguments
            let self_ty = Type::Named(type_name.to_string());
            let instantiated = instantiate_mixin(
                mixin_info,
                &mixin_ref.type_args,
                self_ty
            )?;
            
            // Collect fields (later ones override earlier)
            for (name, ty) in instantiated.fields {
                if seen.contains(&name) {
                    // Check for conflict
                    let existing_ty = fields.iter()
                        .find(|(n, _)| n == &name)
                        .map(|(_, t)| t);
                    if let Some(existing) = existing_ty {
                        if existing != &ty {
                            return Err(TypeError::FieldConflict {
                                field: name,
                                ty1: existing.clone(),
                                ty2: ty,
                            });
                        }
                    }
                }
                seen.insert(name.clone());
                fields.push((name, ty));
            }
        }
    }
    
    Ok(fields)
}
```

**Tests:** 7 tests
- Collect fields from single mixin
- Collect from multiple mixins
- Override field (same type - OK)
- Conflict field (different type - ERROR)
- Generic mixin field collection
- Field access type inference
- Nested mixin composition

### Step 5: Method Collection (5 hours)

**File:** `src/type/src/checker_check.rs`

**Task:** Collect methods from mixins (similar to fields)

```rust
fn collect_composed_methods(
    &self,
    type_name: &str,
) -> Result<Vec<(String, FunctionType)>, TypeError> {
    // Similar to collect_composed_fields but for methods
    // Check signature conflicts
    // Apply override specifications
}
```

**Tests:** 7 tests
- Collect methods from single mixin
- Collect from multiple mixins
- Override method (same signature - OK)
- Conflict method (different signature - ERROR)
- Generic mixin method collection
- Method call type inference
- Override specification (hide/rename)

### Step 6: Required Method Validation (4 hours)

**File:** `src/type/src/checker_check.rs`

**Task:** Validate composing type provides required methods

```rust
fn check_required_methods(
    &self,
    type_name: &str,
    type_methods: &[(String, FunctionType)],
) -> Result<(), TypeError> {
    if let Some(mixins) = self.compositions.get(type_name) {
        for mixin_ref in mixins {
            let mixin_info = self.mixins.get(&mixin_ref.name)?;
            
            for req in &mixin_info.required_methods {
                // Check if type provides this method
                let found = type_methods.iter().any(|(name, fty)| {
                    name == &req.name &&
                    fty.params == req.params &&
                    fty.ret == req.ret
                });
                
                if !found {
                    return Err(TypeError::MissingRequiredMethod {
                        mixin: mixin_info.name.clone(),
                        method: req.name.clone(),
                    });
                }
            }
        }
    }
    Ok(())
}
```

**Tests:** 5 tests
- Required method satisfied
- Required method missing - ERROR
- Required method wrong signature - ERROR
- Generic required method
- Multiple required methods

### Step 7: Trait Requirement Validation (3 hours)

**File:** `src/type/src/checker_check.rs`

**Task:** Validate composing type implements required traits

```rust
fn check_required_traits(
    &self,
    type_name: &str,
) -> Result<(), TypeError> {
    if let Some(mixins) = self.compositions.get(type_name) {
        for mixin_ref in mixins {
            let mixin_info = self.mixins.get(&mixin_ref.name)?;
            
            for trait_name in &mixin_info.required_traits {
                // Check if type implements trait
                if !self.implements_trait(type_name, trait_name) {
                    return Err(TypeError::MissingRequiredTrait {
                        mixin: mixin_info.name.clone(),
                        trait_name: trait_name.clone(),
                    });
                }
            }
        }
    }
    Ok(())
}
```

**Tests:** 4 tests
- Required trait satisfied
- Required trait missing - ERROR
- Multiple required traits
- Generic trait requirement

### Step 8: Field Access Type Inference (3 hours)

**File:** `src/type/src/checker_infer.rs`

**Task:** Infer types for field access on composed types

```rust
// In infer_expression for field access
Expr::FieldAccess(obj, field) => {
    let obj_ty = self.infer_expression(obj)?;
    
    match obj_ty {
        Type::Named(type_name) => {
            // Check composed fields
            let composed_fields = self.collect_composed_fields(&type_name)?;
            if let Some((_, field_ty)) = composed_fields.iter()
                .find(|(name, _)| name == field) {
                return Ok(field_ty.clone());
            }
            
            // Fall back to regular field lookup
            /* ... */
        }
        /* ... */
    }
}
```

**Tests:** 3 tests
- Infer field type from mixin
- Infer overridden field type
- Infer generic mixin field type

### Step 9: Method Call Type Inference (3 hours)

**File:** `src/type/src/checker_infer.rs`

**Task:** Infer types for method calls on composed types

```rust
// In infer_expression for method call
Expr::MethodCall(obj, method, args) => {
    let obj_ty = self.infer_expression(obj)?;
    
    match obj_ty {
        Type::Named(type_name) => {
            // Check composed methods
            let composed_methods = self.collect_composed_methods(&type_name)?;
            if let Some((_, method_ty)) = composed_methods.iter()
                .find(|(name, _)| name == method) {
                // Type check arguments and return method return type
                /* ... */
            }
            
            // Fall back to regular method lookup
            /* ... */
        }
        /* ... */
    }
}
```

**Tests:** 3 tests
- Infer method return type from mixin
- Infer overridden method type
- Infer generic mixin method type

### Step 10: Error Messages (2 hours)

**File:** `src/type/src/lib.rs`

**Task:** Add clear error messages for mixin type errors

```rust
pub enum TypeError {
    // ... existing variants ...
    
    // NEW mixin errors
    UnknownMixin(String),
    FieldConflict {
        field: String,
        ty1: Type,
        ty2: Type,
    },
    MethodConflict {
        method: String,
        sig1: FunctionType,
        sig2: FunctionType,
    },
    MissingRequiredMethod {
        mixin: String,
        method: String,
    },
    MissingRequiredTrait {
        mixin: String,
        trait_name: String,
    },
    WrongMixinTypeArgs {
        mixin: String,
        expected: usize,
        got: usize,
    },
}

impl Display for TypeError {
    // ... add display implementations ...
}
```

**Tests:** 2 tests
- Error message formatting
- Error context information

### Step 11: Integration Testing (3 hours)

**File:** `tests/type_system/mixin_tests.rs` (new)

**Task:** End-to-end integration tests

```rust
#[test]
fn test_timestamped_mixin() {
    let source = r#"
        mixin Timestamped:
            created_at: i64
            updated_at: i64
            
            fn mark_updated():
                self.updated_at = unix_time()
        
        class User with Timestamped:
            name: str
    "#;
    
    let result = type_check_source(source);
    assert!(result.is_ok());
    
    // Verify User has all fields
    let user_ty = result.get_type("User");
    assert_has_field(user_ty, "name", Type::Str);
    assert_has_field(user_ty, "created_at", Type::Int);
    assert_has_field(user_ty, "updated_at", Type::Int);
}

// 15+ more integration tests
```

**Tests:** 15+ integration tests covering all features

## Error Handling Strategy

### Conflict Detection
1. **Field conflicts:** Same name, different type → ERROR
2. **Field override:** Same name, same type → OK (last wins)
3. **Method conflicts:** Same name, different signature → ERROR
4. **Method override:** Same name, same signature → OK (last wins)

### Resolution
- User can specify override explicitly in composition
- `class C with M1(override foo), M2(hide bar)`

## Test Suite Summary

Total: **53 tests**

| Category | Tests | Time |
|----------|-------|------|
| Registration | 3 | 2h |
| Substitution | 5 | 4h |
| Composition | 2 | 3h |
| Field Collection | 7 | 5h |
| Method Collection | 7 | 5h |
| Required Methods | 5 | 4h |
| Required Traits | 4 | 3h |
| Field Inference | 3 | 3h |
| Method Inference | 3 | 3h |
| Error Messages | 2 | 2h |
| Integration | 15 | 3h |

## Files to Modify

1. `src/type/src/lib.rs` - Add TypeError variants, substitution
2. `src/type/src/checker_check.rs` - Mixin registration, validation
3. `src/type/src/checker_infer.rs` - Field/method inference
4. `tests/type_system/mixin_tests.rs` - Test suite (new file)

## Success Criteria

- [ ] All 53 tests passing
- [ ] Mixin fields accessible with correct types
- [ ] Mixin methods callable with correct signatures
- [ ] Generic mixins work with type substitution
- [ ] Conflicts detected and reported clearly
- [ ] Required methods validated
- [ ] Required traits validated
- [ ] Override specifications work
- [ ] Integration with BDD specs (29 tests)

## Timeline

- **Days 1-2:** Steps 1-3 (Registration, Substitution, Composition) - 9 hours
- **Days 3-5:** Steps 4-5 (Field/Method Collection) - 10 hours
- **Days 6-7:** Steps 6-7 (Required validation) - 7 hours
- **Days 8-9:** Steps 8-9 (Type Inference) - 6 hours
- **Day 10:** Steps 10-11 (Errors, Integration) - 5 hours
- **Buffer:** 3 hours for debugging

**Total:** 40 hours over 10 days (2 weeks)

## Next Session Checklist

Before starting Phase 2:
1. ✅ Phase 1 complete and tested
2. ✅ All parser tests passing
3. ✅ Documentation complete
4. ✅ Implementation plan ready
5. [ ] Read existing type checker code
6. [ ] Set up test infrastructure
7. [ ] Begin Step 1 (Mixin Registration)

---

**Ready to begin:** 2026-01-08T06:25:00Z  
**Target completion:** 2026-01-18T06:25:00Z (10 days)
