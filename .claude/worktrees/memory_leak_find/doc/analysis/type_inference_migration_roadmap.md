# Type Inference Migration Roadmap

**Date:** 2026-02-03
**Phase:** 8 - Migration Roadmap (Final)
**Status:** ✅ Complete
**Related:** `doc/plan/type_inference_comparison_plan.md`

## Executive Summary

After comprehensive analysis across 7 phases (36 hours of work), we have evaluated the feasibility of migrating from Rust to Simple for type inference.

**Recommendation:** **Option C - Hybrid Approach**
- Keep Rust for production compiler (fast, proven, complete)
- Fix Simple's critical bugs for teaching/prototyping (8 hours)
- Do NOT attempt full self-hosting (200+ hours, significant performance cost)

**Key Finding:** Simple has fundamental gaps that make self-hosting impractical:
- **0% expression inference** (can't infer types from code)
- **3 critical bugs** (broken occurs check, shallow unification)
- **15-40x slower** than Rust (scaling to 50-100x for large codebases)
- **100+ hours** minimum to reach basic viability

---

## Analysis Summary

### Phase 1-7 Findings

| Phase | Focus | Key Metric | Verdict |
|-------|-------|------------|---------|
| **1. Code Reading** | Function mapping | 25 functions compared | 15 Rust functions have no Simple equivalent |
| **2. Algorithm** | Correctness | Soundness | Simple is **unsound** (broken occurs check) |
| **3. Feature Parity** | Completeness | 26% parity | Simple missing 74% of features |
| **4. Performance** | Speed | 15-40x slower | Unacceptable for production |
| **5. Test Coverage** | Quality | 60x fewer tests | Simple tests miss critical bugs |
| **6. Error Reporting** | Usability | 0% error info | Impossible to debug |
| **7. Architecture** | Design | 12x smaller | Simple is educational prototype |

### Critical Gaps Summary

| Gap | Impact | Severity | Effort to Fix |
|-----|--------|----------|---------------|
| **No expression inference** | Can't infer types from code | 🔴 Blocking | 40 hours |
| **Broken occurs check** | Accepts infinite types | 🔴 Correctness | 2 hours |
| **Shallow function unify** | Wrong type checking | 🔴 Correctness | 4 hours |
| **Shallow generic unify** | Wrong type checking | 🔴 Correctness | 2 hours |
| **No compound types** | Can't type-check arrays, tuples | 🟡 Major | 12 hours |
| **No environment** | Can't look up variables | 🟡 Major | 6 hours |
| **No error messages** | Debugging impossible | 🟡 Major | 32 hours |
| **Incomplete tests** | Unknown correctness | 🟡 Major | 40 hours |
| **15+ missing features** | Can't handle full language | 🟢 Future | 80+ hours |

**Total to Basic Viability:** 106 hours (2.5 weeks full-time)
**Total to Production Quality:** 200+ hours (5 weeks full-time)

---

## Decision Matrix

### Option A: Complete Migration to Simple

**Description:** Implement all missing features in Simple to reach self-hosting capability

**Pros:**
- ✅ Demonstrates self-hosting capability
- ✅ Educational value (shows full compiler in Simple)
- ✅ Simple code easier to understand for newcomers
- ✅ Reduces dependency on Rust expertise

**Cons:**
- ❌ **200+ hours of work** (5 weeks full-time)
- ❌ **15-40x slower** compilation (1s → 15-40s for 10k LOC)
- ❌ **Ongoing maintenance burden** (every Rust improvement must be ported)
- ❌ **Performance regression** (build times 10x slower)
- ❌ **Risk of abandonment** (large investment for uncertain benefit)

**Effort Breakdown:**
| Phase | Tasks | Hours |
|-------|-------|-------|
| 1. Fix bugs | Occurs check, function/generic unification | 8 |
| 2. Add infrastructure | Environment, error types, compound types | 18 |
| 3. Expression inference | 20+ expression cases | 40 |
| 4. Testing | Port Rust tests, add edge cases | 40 |
| 5. Error reporting | Pretty printing, spans, suggestions | 32 |
| 6. Integration | AST conversion, pipeline integration | 16 |
| 7. Advanced features | Effects, traits, macros | 80 |
| 8. Performance tuning | Optimization, profiling | 20 |
| **Total** | | **254 hours** |

**Timeline:** 6-7 weeks full-time

**Risk Assessment:**
- **High risk** of incomplete implementation (scope creep)
- **High risk** of performance issues blocking adoption
- **Medium risk** of bugs in ported code
- **Medium risk** of abandonment midway through

**Recommendation:** ❌ **Not Recommended** - Too much effort for marginal benefit

---

### Option B: Keep Rust Only

**Description:** Maintain status quo - Rust for production, no Simple implementation

**Pros:**
- ✅ **Zero effort** (no work required)
- ✅ **Production-ready** (proven, fast, complete)
- ✅ **Well-tested** (308 tests, 67k lines)
- ✅ **Fast** (sub-second type checking for 10k LOC)
- ✅ **No performance regression**

**Cons:**
- ❌ Not self-hosted (requires Rust knowledge)
- ❌ Harder for newcomers to understand (15+ files)
- ❌ No educational Simple implementation
- ❌ Missed opportunity to demonstrate self-hosting

**Effort:** 0 hours

**Risk Assessment:**
- **Low risk** - Already working
- **No risk** of performance regression
- **No risk** of introducing bugs

**Recommendation:** ✅ **Acceptable** - Safe default choice

---

### Option C: Hybrid Approach (Recommended)

**Description:** Fix Simple's critical bugs for teaching, keep Rust for production

**Pros:**
- ✅ **Minimal effort** (8 hours to fix bugs)
- ✅ **Best of both worlds** (Rust for production, Simple for teaching)
- ✅ **Educational value** (demonstrates core algorithm)
- ✅ **No performance cost** (keep Rust for production)
- ✅ **Low risk** (small changes, isolated)

**Cons:**
- 🟡 Not fully self-hosted (Rust still required)
- 🟡 Maintains two implementations (but Simple is just for teaching)

**Effort Breakdown:**
| Task | Description | Hours |
|------|-------------|-------|
| 1. Fix occurs check | Make it recursive for compound types | 2 |
| 2. Fix function unification | Deep unify params + return | 4 |
| 3. Fix generic unification | Deep unify type arguments | 2 |
| 4. Add critical tests | Tests that expose the bugs | 2 |
| 5. Update documentation | Mark as teaching-only | 1 |
| **Total** | | **11 hours** |

**Timeline:** 1.5 days

**Risk Assessment:**
- **Low risk** - Small, focused changes
- **Low risk** of bugs (well-understood fixes)
- **Low risk** of scope creep (clearly bounded)

**Expected Outcome:**
- Simple becomes **sound** (no infinite types)
- Simple becomes **correct** for basic cases
- Simple remains useful for **teaching/prototyping**
- Rust remains **production compiler**

**Recommendation:** ✅ **RECOMMENDED** - Best ROI

---

## Recommended Path: Option C Implementation

### Phase 1: Fix Critical Bugs (8 hours)

#### Task 1.1: Fix Occurs Check (2 hours)

**Problem:** Only checks top-level Var, doesn't recurse into compounds

**Current Code:**
```simple
fn occurs_check(var_id: i64, ty: Type) -> bool:
    match self.resolve(ty):
        Type.Var(id) -> id == var_id
        _ -> false  # BUG: Should recurse!
```

**Fixed Code:**
```simple
fn occurs_check(var_id: i64, ty: Type) -> bool:
    match self.resolve(ty):
        Type.Var(id) -> id == var_id
        Type.Function(params, ret) ->
            # Recursive check in function (simplified representation)
            # Note: Current Simple stores param_count, not full param types
            # This fix assumes we'll extend Function to store param types
            false  # TODO: Need to extend Type.Function first
        Type.Generic(name, args) ->
            # Recursive check in generic args
            # Note: Current Simple stores arg_count, not full args
            # This fix assumes we'll extend Type.Generic first
            false  # TODO: Need to extend Type.Generic first
        _ -> false
```

**Note:** This reveals a deeper issue - Simple's Type representation is too simplified (stores counts instead of types). Full fix requires extending Type enum.

**Alternative (Better) Fix:**
```simple
# Step 1: Extend Type enum to store full structures
enum Type:
    Int, Bool, Str, Float, Unit
    Var(id: i64)
    Function(params: [Type], ret: Type)  # Changed from (i64, i64)
    Generic(name: str, args: [Type])     # Changed from (str, i64)

# Step 2: Recursive occurs check
fn occurs_check(var_id: i64, ty: Type) -> bool:
    match self.resolve(ty):
        Type.Var(id) -> id == var_id
        Type.Function(params, ret) ->
            params.any(\p: self.occurs_check(var_id, p)) or
            self.occurs_check(var_id, ret)
        Type.Generic(name, args) ->
            args.any(\a: self.occurs_check(var_id, a))
        _ -> false
```

**Effort:** 2 hours (includes extending Type enum)

#### Task 1.2: Fix Function Unification (4 hours)

**Problem:** Only checks param count, doesn't unify param types

**Current Code:**
```simple
(Type.Function(params1, ret1), Type.Function(params2, ret2)) ->
    if params1 != params2:
        false
    else:
        ret1 == ret2  # BUG: Should unify recursively!
```

**Fixed Code:**
```simple
(Type.Function(params1, ret1), Type.Function(params2, ret2)) ->
    if params1.len() != params2.len():
        false
    else:
        # Unify all parameters
        var all_match = true
        for i in 0..params1.len():
            if not self.unify(params1[i], params2[i]):
                all_match = false
                break
        # Unify return types
        all_match and self.unify(ret1, ret2)
```

**Effort:** 4 hours (includes updating Type enum and all call sites)

#### Task 1.3: Fix Generic Unification (2 hours)

**Problem:** Only checks name and arg count, doesn't unify args

**Current Code:**
```simple
(Type.Generic(name1, args1), Type.Generic(name2, args2)) ->
    if name1 != name2:
        false
    else:
        args1 == args2  # BUG: Should unify recursively!
```

**Fixed Code:**
```simple
(Type.Generic(name1, args1), Type.Generic(name2, args2)) ->
    if name1 != name2:
        false
    else if args1.len() != args2.len():
        false
    else:
        # Unify all type arguments
        var all_match = true
        for i in 0..args1.len():
            if not self.unify(args1[i], args2[i]):
                all_match = false
                break
        all_match
```

**Effort:** 2 hours

#### Task 1.4: Add Critical Tests (2 hours)

**Tests to Add:**
```simple
describe "occurs check (fixed)":
    it "detects var in function param":
        var u = TypeUnifier.create()
        val v = u.fresh_var()
        match v:
            Type.Var(id) ->
                val fn_ty = Type.Function([Type.Var(id)], Type.Int)
                expect(u.occurs_check(id, fn_ty)).to(eq(true))

    it "detects var in generic arg":
        var u = TypeUnifier.create()
        val v = u.fresh_var()
        match v:
            Type.Var(id) ->
                val gen_ty = Type.Generic("List", [Type.Var(id)])
                expect(u.occurs_check(id, gen_ty)).to(eq(true))

describe "function unification (fixed)":
    it "detects param type mismatch":
        var u = TypeUnifier.create()
        val fn1 = Type.Function([Type.Int, Type.Bool], Type.Str)
        val fn2 = Type.Function([Type.Float, Type.Int], Type.Str)
        expect(u.unify(fn1, fn2)).to(eq(false))

describe "generic unification (fixed)":
    it "detects arg type mismatch":
        var u = TypeUnifier.create()
        val list_int = Type.Generic("List", [Type.Int])
        val list_bool = Type.Generic("List", [Type.Bool])
        expect(u.unify(list_int, list_bool)).to(eq(false))
```

**Effort:** 2 hours

### Phase 2: Documentation (1 hour)

#### Task 2.1: Update Module Header

Add clear documentation about limitations:

```simple
"""
# Type Inference Engine - Version 3

**Status:** Educational / Prototyping Only
**Production Use:** See Rust implementation in rust/type/

## Purpose

This module demonstrates the core Hindley-Milner type inference algorithm
with Robinson unification. It's designed for:
- Teaching type theory concepts
- Prototyping new type system features
- Understanding the algorithm at a high level

## Limitations

This implementation is NOT suitable for production use:
- ❌ No expression inference (can only unify explicit types)
- ❌ No integration with parser/compiler
- ❌ Limited type system (no arrays, tuples, optionals, dicts, unions)
- ❌ No error messages (returns bool only)
- ❌ 15-40x slower than Rust implementation
- ❌ Missing advanced features (effects, traits, macros)

## For Production

Use the Rust implementation:
- rust/type/src/checker_infer.rs - Expression inference
- rust/type/src/checker_unify.rs - Unification
- rust/type/src/checker_check.rs - Type checking

## Testing

This module includes 60+ built-in tests that run on load.
See test output for verification.
"""
```

**Effort:** 1 hour

---

## Alternative Path: Option A (Full Migration)

**If you decide to pursue full self-hosting despite recommendations, here's the roadmap:**

### Phase 1: Fix Bugs (8 hours) ✅ Same as Option C

### Phase 2: Add Infrastructure (18 hours)

#### 2.1: Add Environment (6 hours)
```simple
class TypeChecker:
    unifier: TypeUnifier
    env: Dict<str, Type>  # Variable → Type mapping

    me add_binding(name: str, ty: Type):
        self.env[name] = ty

    fn lookup(name: str) -> Type?:
        self.env.get(name)
```

#### 2.2: Add Error Types (4 hours)
```simple
enum TypeError:
    Undefined(name: str)
    Mismatch(expected: Type, found: Type)
    OccursCheck(var_id: i64, ty: Type)
    Other(message: str)
```

#### 2.3: Add Compound Types (8 hours)
```simple
enum Type:
    # ... existing
    Array(elem: Type)
    Tuple(elems: [Type])
    Optional(inner: Type)
    Dict(key: Type, value: Type)
```

### Phase 3: Expression Inference (40 hours)

#### 3.1: Literal Inference (2 hours)
```simple
fn infer_expr(expr: Expr) -> Result<Type, TypeError>:
    match expr:
        Expr.Integer(_) -> Ok(Type.Int)
        Expr.Float(_) -> Ok(Type.Float)
        Expr.String(_) -> Ok(Type.Str)
        Expr.Bool(_) -> Ok(Type.Bool)
```

#### 3.2: Variable Inference (4 hours)
```simple
Expr.Identifier(name) ->
    match self.lookup(name):
        Some(ty) -> Ok(ty)
        None -> Err(TypeError.Undefined(name))
```

#### 3.3: Binary Operators (8 hours)
```simple
Expr.Binary(left, op, right) ->
    val left_ty = self.infer_expr(left)?
    val right_ty = self.infer_expr(right)?
    match op:
        Op.Add | Op.Sub | Op.Mul | Op.Div ->
            self.unify(left_ty, right_ty)?
            Ok(left_ty)
        Op.Lt | Op.Gt | Op.Eq ->
            self.unify(left_ty, right_ty)?
            Ok(Type.Bool)
        # ... more operators
```

#### 3.4: Function Calls (6 hours)
```simple
Expr.Call(callee, args) ->
    val callee_ty = self.infer_expr(callee)?
    val arg_tys = args.map(\a: self.infer_expr(a)?)
    match callee_ty:
        Type.Function(params, ret) ->
            for (arg_ty, param_ty) in zip(arg_tys, params):
                self.unify(arg_ty, param_ty)?
            Ok(ret)
        _ -> Err(TypeError.Other("not a function"))
```

#### 3.5: Arrays (4 hours)
#### 3.6: If Expressions (4 hours)
#### 3.7: Match Expressions (6 hours)
#### 3.8: Remaining Cases (6 hours)

### Phase 4: Testing (40 hours)
- Port 100+ Rust tests
- Add edge case tests
- Add error tests
- Add integration tests

### Phase 5: Error Reporting (32 hours)
- Span tracking
- Pretty printing
- Error formatting
- Suggestions

### Phase 6: Integration (16 hours)
- AST conversion
- Parser integration
- Pipeline hookup

### Phase 7: Advanced Features (80 hours)
- Effects system
- Trait checking
- Macro validation

### Phase 8: Performance (20 hours)
- Profiling
- Optimization
- Caching

**Total:** 254 hours (6-7 weeks full-time)

---

## Risk Mitigation

### Risks for Option A (Full Migration)

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| **Performance too slow** | High | High | Profile early; may need JIT or compilation |
| **Incomplete implementation** | Medium | High | Prioritize MVP features first |
| **Bugs in ported code** | High | Medium | Port tests alongside code |
| **Scope creep** | High | Medium | Strict feature freeze after MVP |
| **Abandonment** | Medium | High | Set clear completion criteria upfront |
| **User resistance** | Low | Medium | Communicate performance trade-offs |

### Risks for Option C (Hybrid)

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| **Bugs in fixes** | Low | Low | Comprehensive tests |
| **Type enum extension breaks things** | Low | Medium | Update all call sites carefully |
| **Scope creep** | Low | Low | Clearly bounded (just bug fixes) |

---

## Success Criteria

### For Option C (Hybrid) ✅ Recommended

**Phase 1 Complete:**
- ✅ Occurs check detects infinite types
- ✅ Function unification checks all parameters
- ✅ Generic unification checks all arguments
- ✅ All tests pass (including new critical tests)
- ✅ No known bugs

**Phase 2 Complete:**
- ✅ Documentation updated with limitations
- ✅ Clear marking as "teaching only"

**Overall Success:**
- Simple is **sound** (no infinite types accepted)
- Simple is **correct** for basic unification
- Simple remains **useful for teaching**
- Rust remains **production compiler**
- **Total effort: 11 hours** (achieved in 1.5 days)

### For Option A (Full Migration)

**MVP Complete:**
- ✅ All 3 critical bugs fixed
- ✅ Expression inference for 10+ cases
- ✅ 50+ tests ported from Rust
- ✅ Basic error messages
- ✅ Can type-check simple programs (100 LOC)

**Production Ready:**
- ✅ Expression inference for 20+ cases
- ✅ 100+ tests ported
- ✅ Rich error messages with spans
- ✅ Can type-check medium programs (1,000 LOC)
- ✅ Performance within 20x of Rust

**Unlikely to Achieve:**
- Can type-check large programs (10,000+ LOC) - performance too slow
- Feature parity with Rust - too much work
- Performance within 5x of Rust - fundamental interpreter limitations

---

## Timeline Summary

### Option C (Hybrid) - RECOMMENDED ✅

```
Week 1:
  Days 1-2: Fix bugs (8h) + Documentation (1h)
  Days 3-5: Buffer / Testing

Total: 1-2 weeks with buffer
```

### Option B (Keep Rust Only)

```
Immediate: No work required
```

### Option A (Full Migration) - NOT RECOMMENDED ❌

```
Week 1-2: Fix bugs + Infrastructure (26h)
Week 3-4: Expression inference (40h)
Week 5: Testing (40h)
Week 6: Error reporting (32h)
Week 7: Integration + Advanced features (96h)

Total: 7 weeks (optimistic)
More realistic: 10-12 weeks with debugging
```

---

## Final Recommendation

### Recommended Approach: Option C (Hybrid)

**Actions:**
1. **Immediate (11 hours):**
   - Fix 3 critical bugs in Simple
   - Add documentation marking it as teaching-only
   - Keep Rust for production

2. **Short Term (0 hours):**
   - Continue using Rust for production compiler
   - Use Simple for teaching type theory
   - No performance regression

3. **Long Term (Optional):**
   - If self-hosting becomes critical, revisit in 1-2 years
   - By then, may have JIT or better performance story
   - Or accept 10x slower build times as cost of self-hosting

**Benefits:**
- ✅ **Minimal effort** (11 hours)
- ✅ **No performance cost** (keep Rust)
- ✅ **Educational value** (Simple becomes sound)
- ✅ **Low risk** (small, focused changes)
- ✅ **Best ROI** (maximum benefit for minimum effort)

**Trade-offs:**
- 🟡 Not fully self-hosted (but impractical anyway)
- 🟡 Two implementations to maintain (but Simple is teaching-only)

### Why Not Option A?

- ❌ **200+ hours** - Too much effort
- ❌ **15-40x slower** - Unacceptable performance cost
- ❌ **High risk** - Many unknowns, likely to stall
- ❌ **Unclear benefit** - Self-hosting is more symbolic than practical

### Why Not Option B?

- ✅ **Acceptable** but missed opportunity
- Simple has bugs that should be fixed for teaching use
- 11 hours of work is worthwhile investment

---

## Conclusion

After 36 hours of comprehensive analysis covering:
- ✅ Function mapping (25 functions compared)
- ✅ Algorithm correctness (found 3 critical bugs)
- ✅ Feature parity (26% complete)
- ✅ Performance analysis (15-40x slower)
- ✅ Test coverage (60x fewer tests)
- ✅ Error reporting (0% vs 92%)
- ✅ Architecture comparison (12x smaller)

**We recommend Option C: Hybrid Approach**

**Action Items:**
1. Fix Simple's 3 critical bugs (8 hours)
2. Add documentation about limitations (1 hour)
3. Keep Rust for production (0 hours)
4. Use Simple for teaching only (ongoing)

**Total Effort:** 11 hours (1.5 days)

**Expected Outcome:**
- Simple becomes **sound and correct** for teaching
- Rust remains **fast and complete** for production
- **Best of both worlds** achieved
- **No performance regression**
- **Minimal risk and effort**

---

**Documents:**
- **This Document:** `doc/analysis/type_inference_migration_roadmap.md`
- Architecture: `doc/analysis/type_inference_architecture.md`
- Error Reporting: `doc/analysis/type_inference_error_reporting.md`
- Test Coverage: `doc/analysis/type_inference_test_coverage.md`
- Performance: `doc/analysis/type_inference_performance.md`
- Feature Parity: `doc/analysis/type_inference_feature_parity.md`
- Algorithm Comparison: `doc/analysis/type_inference_algorithm_comparison.md`
- Function Mapping: `doc/analysis/type_inference_function_mapping.md`
- Initial Observations: `doc/analysis/type_inference_initial_observations.md`
- Summary: `doc/analysis/type_inference_comparison_summary.md`

**Status:** ✅ **ANALYSIS COMPLETE** (All 8 Phases Done)
**Recommendation:** Proceed with Option C (Hybrid Approach)
