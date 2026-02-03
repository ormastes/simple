# FFI Coverage Status Report

**Date:** 2026-02-04
**Status:** Partial coverage with gaps in app-level utilities

## Summary

| Metric | Count | Percentage |
|--------|-------|------------|
| **Rust FFI implementations** | 1,016 | 100% |
| **Simple extern declarations** | 291 | 29% |
| **Simple wrapper functions** | 104 | 36% of declared |
| **Missing from Simple** | 725 | 71% |

## Coverage Breakdown

### Current Coverage (291 extern declarations)

**Well-Covered Categories:**
- ✅ File I/O (13 functions) - good coverage
- ✅ Directory (5 functions) - good coverage
- ✅ Process execution (4 functions) - basic coverage
- ✅ Environment (3 functions) - basic coverage
- ✅ Time/Timestamp (7 functions) - good coverage
- ✅ System info (4 functions) - good coverage
- ✅ CLI delegation (60+ functions) - extensive coverage
- ✅ Cargo build system (7 functions) - good coverage
- ✅ Coverage (3 functions) - good coverage

### Missing but SHOULD Wrap (App-Level Utilities)

**Priority 1: Essential App Utilities**

| Category | Missing | Examples | Priority |
|----------|---------|----------|----------|
| **Math** | 36 | sin, cos, sqrt, abs, ceil, floor | HIGH |
| **String** | 15 | split, join, replace, char_at | HIGH |
| **Array** | 36 | map, filter, reduce, first, last | HIGH |
| **Dictionary** | 8 | get, set, keys, values, clear | HIGH |
| **Random** | 5 | random, seed, next | MEDIUM |
| **SDN** | 3 | fmt, from_json, version | MEDIUM |
| **Timestamp extended** | 4 | add_days, diff_days, from_components | LOW |

**Total:** ~107 functions should be wrapped

**Priority 2: Concurrency (Selective)**
- Atomic operations (10-15 useful ones from 80 total)
- Channel operations (if not already in stdlib)
- Mutex/RWLock (if not already in stdlib)

**Total:** ~15-20 concurrency functions

### Missing and SHOULD NOT Wrap (Library/Internal)

**Correctly excluded:**

| Category | Count | Reason |
|----------|-------|--------|
| **Vulkan/GPU** | 65 | Library bindings - keep in Rust |
| **CUDA/GPU** | 20 | Library bindings - keep in Rust |
| **OpenGL** | ~20 | Library bindings - keep in Rust |
| **AST/Parser** | ~100 | Compiler internals - not for apps |
| **Runtime Value** | ~200 | Runtime internals - not for apps |
| **Codegen** | ~50 | Compiler internals - not for apps |
| **Garbage Collection** | ~10 | Runtime internals - not for apps |
| **Actors** | ~30 | Runtime internals - may be stdlib |

**Total:** ~500 functions correctly excluded

## Wrapper Function Coverage

Of the 291 extern declarations, only 104 have wrapper functions:

**Wrapper coverage: 36%**

### Missing Wrappers (187 extern declarations without wrappers)

These `extern fn` declarations exist but lack Simple wrapper functions:

**Parser/AST Functions (100+):**
- rt_ast_* (50+ functions)
- rt_parser_* (20+ functions)
- rt_lexer_* (15+ functions)

**Runtime Functions (60+):**
- rt_args_get
- rt_exit_hook_register
- rt_bdd_* functions
- rt_sspec_* functions

**Other (20+):**
- rt_eval, rt_eval_expr
- rt_panic
- rt_readline
- etc.

## Issues Identified

### 1. Missing Essential App Utilities ⚠️

**Math functions not wrapped:**
```simple
# These should exist but don't:
fn abs(x: f64) -> f64
fn sin(x: f64) -> f64
fn sqrt(x: f64) -> f64
fn ceil(x: f64) -> f64
# ... 32 more math functions
```

**String operations not wrapped:**
```simple
# These should exist but don't:
fn string_split(s: text, delimiter: text) -> [text]
fn string_join(parts: [text], separator: text) -> text
fn string_replace(s: text, from: text, to: text) -> text
# ... 12 more string functions
```

**Array operations not wrapped:**
```simple
# These should exist but don't:
fn array_first<T>(arr: [T]) -> T?
fn array_last<T>(arr: [T]) -> T?
fn array_slice<T>(arr: [T], start: i64, end: i64) -> [T]
# ... 33 more array functions
```

### 2. Incomplete Wrapper Coverage ⚠️

Many extern functions declared but not wrapped means they can't be used safely from Simple apps.

### 3. Categorization Issues

The "Other" category (589 functions) is too large. Many are:
- Actor runtime functions (should be in stdlib, not FFI)
- BDD/SSpec functions (should be in testing stdlib)
- Value manipulation (runtime internals)

## Recommendations

### Immediate Actions

**1. Wrap Essential Math Functions (36 functions)**

Create `src/std/math/mod.spl`:
```simple
extern fn rt_math_sin(x: f64) -> f64
fn sin(x: f64) -> f64:
    rt_math_sin(x)

extern fn rt_math_sqrt(x: f64) -> f64
fn sqrt(x: f64) -> f64:
    rt_math_sqrt(x)

# ... 34 more
```

**2. Wrap Essential String Functions (15 functions)**

Extend `src/std/text/mod.spl`:
```simple
extern fn rt_string_split(s: text, delim: text) -> [text]
fn split(s: text, delimiter: text) -> [text]:
    rt_string_split(s, delimiter)

# ... 14 more
```

**3. Wrap Essential Array Functions (36 functions)**

Create `src/std/array/mod.spl`:
```simple
extern fn rt_array_first<T>(arr: [T]) -> T?
fn first<T>(arr: [T]) -> T?:
    rt_array_first(arr)

# ... 35 more
```

**4. Wrap Dictionary Functions (8 functions)**

Create `src/std/dict/mod.spl`:
```simple
extern fn rt_dict_new() -> {K: V}
fn new<K, V>() -> {K: V}:
    rt_dict_new()

# ... 7 more
```

### Medium-Term Actions

**5. Review Parser/AST Functions**

Currently 100+ parser/AST extern functions without wrappers. Options:
- a) Wrap them for metaprogramming use cases
- b) Keep them internal-only
- **Recommend:** Option (b) - these are compiler internals

**6. Review Actor/Runtime Functions**

Currently 30+ actor functions. These should be:
- Moved to stdlib as proper Simple APIs
- Not exposed as raw FFI

**7. Consolidate Concurrency Primitives**

Currently 80 concurrency functions. Review and wrap only:
- Atomic operations (10-15 essential ones)
- High-level primitives (Channel, Mutex if not in stdlib)

### Long-Term Strategy

**Three-Tier Architecture:**

1. **Tier 1: Runtime/Internal (NO wrapping)**
   - GC, Value, Actors, Codegen
   - Keep as Rust-only

2. **Tier 2: Library Bindings (NO wrapping)**
   - GPU (Vulkan, CUDA, OpenGL)
   - External C libraries
   - Keep as Rust-only

3. **Tier 3: App Utilities (WRAP ALL)**
   - Math, String, Array, Dict
   - File, Process, Network
   - All app-facing utilities

**Current status:** Missing ~120 Tier 3 functions

## Action Plan

### Phase 1: Essential Utilities (1-2 days)
- [ ] Wrap Math functions (36)
- [ ] Wrap String functions (15)
- [ ] Wrap Array functions (36)
- [ ] Wrap Dictionary functions (8)

**Total:** 95 wrappers

### Phase 2: Extended Utilities (1 day)
- [ ] Wrap Random functions (5)
- [ ] Wrap SDN functions (3)
- [ ] Wrap Timestamp extended (4)
- [ ] Select and wrap essential Concurrency (15)

**Total:** 27 wrappers

### Phase 3: Cleanup (1 day)
- [ ] Audit existing 187 unwrapped externs
- [ ] Remove compiler-internal externs from app modules
- [ ] Document FFI categorization
- [ ] Update CLAUDE.md with FFI guidelines

## Files to Create/Update

1. **Create:** `src/std/math/mod.spl` (36 wrappers)
2. **Create:** `src/std/array/mod.spl` (36 wrappers)
3. **Create:** `src/std/dict/mod.spl` (8 wrappers)
4. **Update:** `src/std/text/mod.spl` (add 15 wrappers)
5. **Update:** `src/std/random/mod.spl` (add 5 wrappers)
6. **Update:** `doc/guide/ffi_guidelines.md` (document three-tier architecture)

## Conclusion

**Current FFI coverage is incomplete for app development.**

While compiler-internal and GPU functions are correctly excluded, essential app utilities (Math, String, Array, Dict) are missing.

**Estimated work:** 3-4 days to complete Phase 1-3
**Impact:** Enables proper Simple app development without raw FFI calls

**Priority:** HIGH - Math and Array functions are essential for most apps
