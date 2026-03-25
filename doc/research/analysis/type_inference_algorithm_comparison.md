# Type Inference Algorithm Comparison - Rust vs Simple

**Date:** 2026-02-03
**Phase:** 2 - Algorithm Comparison
**Related:** `doc/plan/type_inference_comparison_plan.md`, `doc/analysis/type_inference_function_mapping.md`

## Executive Summary

Both implementations use **Hindley-Milner type inference** with **Robinson unification algorithm**. The core algorithms are identical, but Rust has a complete implementation while Simple has a minimal proof-of-concept with critical bugs and missing features.

**Key Finding:** Simple's occurs check is **broken** - it will accept infinite types.

---

## Algorithm Flowcharts

### Rust Type Inference Pipeline

```
┌─────────────────────────────────────────────────────────────┐
│                    TYPE INFERENCE PIPELINE                   │
└─────────────────────────────────────────────────────────────┘

Input: Expr (AST expression)
  │
  ├─→ infer_expr(expr) ───────────────────────────────────┐
  │                                                         │
  │   Match on expression type:                            │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ Literal (Int, Float, Str, Bool, Nil)         │    │
  │   │   ↓                                           │    │
  │   │   Return primitive type directly              │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ Identifier (variable reference)              │    │
  │   │   ↓                                           │    │
  │   │   env.get(name) ──→ Some(ty) ──→ Return ty   │    │
  │   │                  └→ None ──→ Error(Undefined) │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ Binary(left, op, right)                      │    │
  │   │   ↓                                           │    │
  │   │   left_ty ← infer_expr(left)                 │    │
  │   │   right_ty ← infer_expr(right)               │    │
  │   │   ↓                                           │    │
  │   │   Match op:                                   │    │
  │   │     Arithmetic → unify(left_ty, right_ty)    │    │
  │   │                  return left_ty               │    │
  │   │     Comparison → unify(left_ty, right_ty)    │    │
  │   │                  return Bool                  │    │
  │   │     Logical    → unify(left_ty, Bool)        │    │
  │   │                  unify(right_ty, Bool)       │    │
  │   │                  return Bool                  │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ Call(callee, args)                           │    │
  │   │   ↓                                           │    │
  │   │   callee_ty ← infer_expr(callee)             │    │
  │   │   arg_tys ← [infer_expr(a) for a in args]    │    │
  │   │   ↓                                           │    │
  │   │   Match callee_ty:                           │    │
  │   │     Function{params, ret} →                  │    │
  │   │       for (arg_ty, param_ty) in zip:        │    │
  │   │         unify(arg_ty, param_ty)              │    │
  │   │       return ret                             │    │
  │   │     _ → return fresh_var()                   │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ Array([items])                               │    │
  │   │   ↓                                           │    │
  │   │   if items.is_empty():                       │    │
  │   │     elem_ty ← fresh_var()                    │    │
  │   │   else:                                       │    │
  │   │     elem_ty ← infer_expr(items[0])           │    │
  │   │     for item in items[1..]:                  │    │
  │   │       unify(elem_ty, infer_expr(item))       │    │
  │   │   return Array(elem_ty)                      │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ... 15+ more expression types ...                    │
  │                                                         │
  └────────────────────────────────────────────────────────┘
                            │
                            ↓
                       Result<Type, TypeError>
```

### Simple Unification Only

```
┌─────────────────────────────────────────────────────────────┐
│                    UNIFICATION ONLY                          │
└─────────────────────────────────────────────────────────────┘

Input: (Type, Type) - already known types
  │
  ├─→ unify(t1, t2) ──────────────────────────────────────┐
  │                                                         │
  │   Step 1: Resolve both types                           │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ resolved_t1 ← resolve(t1)                    │    │
  │   │ resolved_t2 ← resolve(t2)                    │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   Step 2: Check if already equal                       │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ if resolved_t1 == resolved_t2:               │    │
  │   │   return true                                │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   Step 3: Match on type pair                           │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ (Var(id1), Var(id2))                         │    │
  │   │   ↓                                           │    │
  │   │   if id1 == id2: return true                 │    │
  │   │   else:                                       │    │
  │   │     substitution[id1] = Var(id2)             │    │
  │   │     return true                              │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ (Var(id), other) or (other, Var(id))         │    │
  │   │   ↓                                           │    │
  │   │   if occurs_check(id, other):                │    │
  │   │     return false  // infinite type          │    │
  │   │   else:                                       │    │
  │   │     substitution[id] = other                 │    │
  │   │     return true                              │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ (Function(c1, r1), Function(c2, r2))         │    │
  │   │   ↓                                           │    │
  │   │   if c1 != c2: return false                  │    │
  │   │   return r1 == r2  // SHALLOW comparison     │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ (Generic(n1, a1), Generic(n2, a2))           │    │
  │   │   ↓                                           │    │
  │   │   if n1 != n2: return false                  │    │
  │   │   return a1 == a2  // SHALLOW comparison     │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  │   ┌──────────────────────────────────────────────┐    │
  │   │ _ (all other cases)                          │    │
  │   │   ↓                                           │    │
  │   │   return false  // type mismatch             │    │
  │   └──────────────────────────────────────────────┘    │
  │                                                         │
  └────────────────────────────────────────────────────────┘
                            │
                            ↓
                         bool
```

---

## Side-by-Side Execution Trace

### Example Program

```simple
fn identity<T>(x: T) -> T:
    x

val result = identity(42)
```

**Expected:** Infer `result: i32` (or `Int`)

---

### Rust Execution Trace

```
=== PHASE 1: Parse ===
AST:
  FnDef {
    name: "identity",
    type_params: ["T"],
    params: [("x", TypeParam("T"))],
    ret: TypeParam("T"),
    body: Identifier("x")
  }
  VarDecl {
    name: "result",
    value: Call(Identifier("identity"), [Integer(42)])
  }

=== PHASE 2: Register Functions ===
env.insert("identity", Function {
  params: [TypeParam("T")],
  ret: TypeParam("T")
})

=== PHASE 3: Infer 'result' ===
Step 1: infer_expr(Call(Identifier("identity"), [Integer(42)]))

  Step 1.1: Infer callee
    infer_expr(Identifier("identity"))
    → env.get("identity")
    → Function { params: [TypeParam("T")], ret: TypeParam("T") }

  Step 1.2: Instantiate generic
    Create fresh var: α₀
    Instantiate: Function { params: [α₀], ret: α₀ }

  Step 1.3: Infer arguments
    arg_tys = [infer_expr(Integer(42))]
           = [Int]

  Step 1.4: Unify parameters
    unify(Int, α₀)
    → subst[α₀] = Int

  Step 1.5: Return type
    resolve(α₀)
    → apply_subst(α₀, {α₀: Int})
    → Int

Result: result: Int ✓

=== PHASE 4: Substitution State ===
subst = { α₀: Int }
env = { "identity": Function{...}, "result": Int }
```

---

### Simple Execution (Hypothetical - doesn't have expression inference)

```
=== SIMPLE CANNOT EXECUTE THIS ===

Reason: No expression inference (infer_expr doesn't exist)

What Simple CAN do:
  - unify(Int, Int) → true
  - unify(Var(0), Int) → true, subst[0] = Int
  - unify(Function(1, 0), Function(1, 0)) → true

What Simple CANNOT do:
  - Infer type of 42 (no literal inference)
  - Look up "identity" type (no environment)
  - Instantiate generics (no instantiation logic)
  - Infer call result type (no call inference)

Conclusion: Simple needs 20+ hours of work to add expression inference
           before it can handle even this trivial example.
```

---

## Unification Algorithm Detailed Comparison

### Test Case 1: Primitive Unification

**Input:** `unify(Int, Int)`

**Rust:**
```
1. apply_subst(Int, {}) → Int
2. apply_subst(Int, {}) → Int
3. match (Int, Int):
     (Type::Int, Type::Int) → Ok(())
   ✓ Success
```

**Simple:**
```
1. resolve(Int) → Int
2. resolve(Int) → Int
3. Int == Int → true (early return)
   ✓ Success
```

**Result:** ✅ Both correct

---

### Test Case 2: Variable Unification

**Input:** `unify(Var(α), Int)`

**Rust:**
```
1. apply_subst(Var(α), {}) → Var(α)
2. apply_subst(Int, {}) → Int
3. match (Var(α), Int):
     (Type::Var(id), ty) →
       occurs_check: Int.contains_var(α) → false
       subst.insert(α, Int)
       Ok(())
   ✓ Success, subst = {α: Int}
```

**Simple:**
```
1. resolve(Var(α)) → Var(α)
2. resolve(Int) → Int
3. Var(α) == Int → false
4. match (Var(α), Int):
     (Type.Var(id), other) →
       occurs_check(α, Int) → false
       substitution[α] = Int
       true
   ✓ Success, substitution = {α: Int}
```

**Result:** ✅ Both correct

---

### Test Case 3: Occurs Check (Critical)

**Input:** `unify(Var(α), Function([Var(α)], Int))`
**Expectation:** Fail (infinite type: α = fn(α) -> Int)

**Rust:**
```
1. apply_subst(Var(α), {}) → Var(α)
2. apply_subst(Function([Var(α)], Int), {}) → Function([Var(α)], Int)
3. match (Var(α), Function([Var(α)], Int)):
     (Type::Var(id), ty) →
       occurs_check:
         ty.contains_var(α) →
           Function([Var(α)], Int).contains_var(α) →
             params.any(|p| p.contains_var(α)) →
               Var(α).contains_var(α) → true
         → true (infinite type detected!)
       Err(OccursCheck { var_id: α, ty: Function(...) })
   ✓ Success: Correctly rejects infinite type
```

**Simple:**
```
1. resolve(Var(α)) → Var(α)
2. resolve(Function([Var(α)], Int)) → Function([Var(α)], Int)
   Note: Simple has Function(param_count, return_id) not Function([Type], Type)
   So this would be: Function(1, ???)
   Let's assume: Function(1, 5) where 5 is some type ID

3. Var(α) == Function(1, 5) → false
4. match (Var(α), Function(1, 5)):
     (Type.Var(id), other) →
       occurs_check(α, Function(1, 5)):
         resolve(Function(1, 5)) → Function(1, 5)
         match Function(1, 5):
           _ → false  // NOT a Var, returns false!
       → false (no infinite type detected)
       substitution[α] = Function(1, 5)
       true
   ❌ FAILURE: Accepts infinite type!
```

**Result:** ❌ **Simple has critical bug** - occurs check only checks top-level Var

---

### Test Case 4: Function Type Unification

**Input:** `unify(Function([Int, Bool], Str), Function([Float, Int], Char))`
**Expectation:** Fail (parameter types don't match, return types don't match)

**Rust:**
```
1. Resolve both types (no substitutions)
2. match (Function([Int, Bool], Str), Function([Float, Int], Char)):
     params.len() == params.len() → 2 == 2 ✓
     for (Int, Float): unify(Int, Float) → Err(Mismatch)
   ✓ Success: Correctly detects mismatch
```

**Simple:**
```
1. resolve both → no change
2. Var check → neither is Var
3. match (Function(2, ???), Function(2, ???)):
     (Function(c1, r1), Function(c2, r2)) →
       if c1 != c2: return false
       → 2 == 2, continue
       return r1 == r2
       → depends on whether return type IDs match
   ❌ FAILURE: Never checks parameter types!
```

**Result:** ❌ **Simple has semantic bug** - doesn't deeply unify function types

---

### Test Case 5: Transitive Substitution

**Input:**
```
unify(Var(α), Var(β))
unify(Var(β), Var(γ))
unify(Var(γ), Int)
resolve(Var(α))
```

**Expected:** `Int`

**Rust:**
```
Step 1: unify(Var(α), Var(β))
  → subst = {α: Var(β)}

Step 2: unify(Var(β), Var(γ))
  → subst = {α: Var(β), β: Var(γ)}

Step 3: unify(Var(γ), Int)
  → subst = {α: Var(β), β: Var(γ), γ: Int}

Step 4: resolve(Var(α))
  → apply_subst(Var(α), subst)
  → apply_subst(Var(β), subst)  // Follow α -> β
  → apply_subst(Var(γ), subst)  // Follow β -> γ
  → apply_subst(Int, subst)     // Follow γ -> Int
  → Int
  ✓ Correct: Int
```

**Simple:**
```
Step 1: unify(Var(α), Var(β))
  → substitution = {α: Var(β)}

Step 2: unify(Var(β), Var(γ))
  → substitution = {α: Var(β), β: Var(γ)}

Step 3: unify(Var(γ), Int)
  → substitution = {α: Var(β), β: Var(γ), γ: Int}

Step 4: resolve(Var(α))
  → substitution.get(α) → Some(Var(β))
  → resolve(Var(β))
  → substitution.get(β) → Some(Var(γ))
  → resolve(Var(γ))
  → substitution.get(γ) → Some(Int)
  → resolve(Int)
  → Int
  ✓ Correct: Int
```

**Result:** ✅ Both correct (transitive resolution works)

---

## Complexity Analysis

### Time Complexity

| Operation | Rust | Simple | Notes |
|-----------|------|--------|-------|
| **fresh_var()** | O(1) | O(1) | Counter increment |
| **resolve(Type)** | O(d × s) | O(d) | Rust recurses into compounds, Simple only follows var chain |
| **unify(Type, Type)** | O(n × log m) | O(1)* | Rust recursive, Simple shallow |
| **occurs_check(id, Type)** | O(n) | O(1)* | Rust recursive, Simple top-level only |
| **infer_expr(Expr)** | O(n × m) | N/A | Rust only, n = expr size, m = unifications |

*Simple's O(1) is because it doesn't properly traverse compound types (bug, not feature!)

**Key:**
- `d` = substitution chain depth
- `s` = compound type size (for recursive substitution)
- `n` = type size (tree depth)
- `m` = substitution map size

### Space Complexity

| Structure | Rust | Simple | Notes |
|-----------|------|--------|-------|
| **Substitution Map** | O(v) | O(v) | v = # of type variables |
| **Environment** | O(e) | O(0) | e = # of bindings (Simple has no environment) |
| **Type Representation** | O(t) | O(1) | Rust stores full structure, Simple stores counts |

---

## Algorithm Correctness Analysis

### Soundness

**Question:** If `unify(t1, t2)` succeeds, are t1 and t2 actually unifiable?

| Implementation | Verdict | Explanation |
|----------------|---------|-------------|
| **Rust** | ✅ Sound | Correctly implements Robinson's algorithm |
| **Simple** | ❌ **Unsound** | Occurs check incomplete - accepts infinite types |

**Example of Simple Unsoundness:**
```
unify(α, List<α>) → true (BUG - should fail)
Result: α = List<α> = List<List<α>> = List<List<List<α>>>... (infinite!)
```

### Completeness

**Question:** If t1 and t2 are unifiable, will `unify(t1, t2)` succeed?

| Implementation | Verdict | Explanation |
|----------------|---------|-------------|
| **Rust** | ✅ Complete | Handles all type constructors |
| **Simple** | ⚠️ **Incomplete** | Missing Array, Tuple, Optional, Dict, Union cases |

**Example of Simple Incompleteness:**
```
t1 = Array(Int), t2 = Array(Int)
Simple: match case not found → returns false (BUG - should succeed)
```

### Termination

**Question:** Does unification always terminate?

| Implementation | Verdict | Explanation |
|----------------|---------|-------------|
| **Rust** | ✅ Terminates | Occurs check prevents infinite recursion |
| **Simple** | ✅ Terminates | No deep recursion (doesn't traverse compounds) |

**Note:** Simple terminates quickly because it doesn't do the work it should!

---

## Summary Table

| Aspect | Rust | Simple | Gap Severity |
|--------|------|--------|--------------|
| **Algorithm** | Hindley-Milner | Hindley-Milner | ✅ Same |
| **Unification** | Robinson | Robinson | ✅ Same |
| **Soundness** | ✅ Sound | ❌ Unsound | 🔴 Critical |
| **Completeness** | ✅ Complete | ⚠️ Incomplete | 🟡 High |
| **Termination** | ✅ Terminates | ✅ Terminates | ✅ OK |
| **Expression Inference** | ✅ Full (20+ cases) | ❌ None | 🔴 Blocking |
| **Type Constructors** | 15+ | 8 | 🟡 High |
| **Error Information** | Rich | None | 🟡 Medium |
| **Test Coverage** | 67k lines | 60 tests | 🟡 High |

---

## Critical Bugs Found in Simple

### 1. 🔴 Broken Occurs Check
**File:** `lib/std/src/type_checker/type_inference_v3.spl:122-128`
**Bug:** Only checks if resolved type is a Var, doesn't traverse compounds
**Impact:** Accepts infinite types like `α = List<α>`
**Fix:** Recursive traversal of all type constructors
**Effort:** 2 hours

### 2. 🔴 Shallow Function Unification
**File:** `lib/std/src/type_checker/type_inference_v3.spl:106-110`
**Bug:** Only checks param count and return ID, doesn't unify parameter types
**Impact:** Accepts `fn(Int)->Bool` = `fn(Str)->Char` if counts match
**Fix:** Deep unification of params + recursive unify on ret
**Effort:** 4 hours

### 3. 🔴 Shallow Generic Unification
**File:** `lib/std/src/type_checker/type_inference_v3.spl:113-117`
**Bug:** Only checks name and arg count, doesn't unify type arguments
**Impact:** Accepts `List<Int>` = `List<Bool>` (wrong!)
**Fix:** Recursive unify on all type arguments
**Effort:** 2 hours

### 4. 🔴 No Expression Inference
**File:** N/A (doesn't exist)
**Bug:** Can't infer types from literals, operators, calls, etc.
**Impact:** Can't type-check any real code
**Fix:** Implement full `infer_expr()` with 20+ cases
**Effort:** 40 hours

---

## Recommendations

### Immediate Fixes (P0 - Correctness)
1. **Fix occurs check** - 2 hours - Make it recursive
2. **Fix function unification** - 4 hours - Deep unify params
3. **Fix generic unification** - 2 hours - Deep unify args

**Total:** 8 hours to fix correctness bugs

### Short Term (P1 - Functionality)
4. **Add Array/Tuple/Optional/Dict types** - 12 hours
5. **Add expression inference skeleton** - 40 hours (literals, identifiers, operators)
6. **Add environment tracking** - 6 hours

**Total:** 58 hours to reach basic functionality

### Medium Term (P2 - Production Ready)
7. **Add error information** - 4 hours (Result type instead of bool)
8. **Add full expression inference** - 20 hours (remaining cases)
9. **Port Rust test suite** - 40 hours (subset of 67k lines)

**Total:** 64 hours for production quality

---

**Phase 2 Status:** ✅ Complete
**Critical Finding:** Simple's occurs check is broken - accepts infinite types
**Next:** Phase 3 - Feature Parity Matrix
