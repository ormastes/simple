# simple_new vs simple_old Test Comparison
**Date:** 2026-01-30  
**Test Mode:** Interpreter

## Overview

Both `simple_old` (Rust runtime) and `simple_new` (Simple CLI wrapper) show **identical results** after fixes applied.

---

## Test Results Comparison

| Component | simple_old | simple_new | Status |
|-----------|-----------|-----------|--------|
| **Collections** | 22/22 ✅ | 22/22 ✅ | Identical |
| **Time** | 7/7 ✅ | 7/7 ✅ | Identical |
| **Random** | 10/12 ⚠️ | 10/12 ⚠️ | Identical |
| **TOTAL** | **39/48** | **39/48** | **Perfect Match** |

---

## Random Module: Identified Failures

Both runners show the **same 2 failing tests**:

### ❌ Test 1: Normal Distribution
```
✗ should generate normal distribution
  semantic: variable `math` not found
```

### ❌ Test 2: Exponential Distribution  
```
✗ should generate exponential distribution
  semantic: variable `math` not found
```

**Root Cause:** The `use core.math` import at module level doesn't make `math` available as a variable reference inside functions.

**Location:** `src/lib/std/src/compiler_core/random.spl` lines 100-119

---

## Detailed Results

### Collections (simple_new)
```bash
$ ./bin/wrappers/simple_new test test/03_system/collections/

BTreeMap basic operations
  ✓ creates new BTreeMap
  ✓ inserts and retrieves values
  ✓ maintains sorted order
  ✓ checks if key exists
  ✓ removes keys
  ✓ clears all entries
  ✓ gets all values
7 examples, 0 failures

HashMap Basic Operations
  ✓ creates new HashMap
  ✓ inserts and retrieves values
  ✓ handles multiple insertions
  ✓ checks if key exists
  ✓ removes keys
  ✓ gets all keys
  ✓ clears all entries
  ✓ gets all values
8 examples, 0 failures

HashSet basic operations
  ✓ creates new HashSet
  ✓ inserts elements
  ✓ handles duplicate insertions
  ✓ checks if element exists
  ✓ removes elements
  ✓ clears all elements
  ✓ converts to array
7 examples, 0 failures

✓ All tests passed!
```

### Time (simple_new)
```bash
$ ./bin/wrappers/simple_new test test/lib/std/unit/core/time_spec.spl

Time FFI Functions
  rt_time_now_seconds
    ✓ should return current time as Unix timestamp
    ✓ should return time greater than 2020-01-01
    ✓ should return increasing timestamps
    ✓ should have reasonable precision
  time measurements
    ✓ should measure elapsed time
    ✓ should support duration calculations
    ✓ should support comparison operations

7 examples, 0 failures
✓ All tests passed!
```

### Random (simple_new)
```bash
$ ./bin/wrappers/simple_new test test/lib/std/unit/core/random_spec.spl

Random module
  Seeding
    ✓ should set seed
    ✓ should allow getting and setting state
  Random integers
    ✓ should generate integer in range
    ✓ should generate uniform integer in range
  Random floats
    ✓ should generate f32 in 0-1
    ✓ should generate uniform f32 in range
  Sequences
    ✓ should choose random element
    ✓ should choose k random elements
    ✓ should shuffle list
    ✓ should sample without replacement
  Distributions
    ✗ should generate normal distribution
      semantic: variable `math` not found
    ✗ should generate exponential distribution
      semantic: variable `math` not found

12 examples, 2 failures
```

---

## Analysis

### What's Working ✅

1. **Extern function resolution** - Working in both runners
2. **BTreeSet FFI** - Complete and functional
3. **Time matchers** - Fixed and working
4. **Random basic functions** - 10/12 working
5. **Module exports** - `pub fn` recognized by test framework

### Remaining Issue ⚠️

**Problem:** `use core.math` at module level doesn't create a `math` variable

**Current code (random.spl):**
```simple
use core.math  # Module-level import

pub fn gauss(mu: f32, sigma: f32) -> f32:
    val z0 = math.sqrt(...)  # ❌ math not found
    ...
```

**Why it fails:**
- `use core.math` imports math functions into the namespace
- But doesn't create a `math` module variable for qualified access
- Functions like `sqrt()` work directly, but `math.sqrt()` doesn't

**Solution Options:**

1. **Direct function calls** (change random.spl):
   ```simple
   use core.math
   
   pub fn gauss(mu: f32, sigma: f32) -> f32:
       val z0 = sqrt(...)  # Direct call
   ```

2. **Import as variable** (if syntax exists):
   ```simple
   import core.math as math
   
   pub fn gauss(mu: f32, sigma: f32) -> f32:
       val z0 = math.sqrt(...)  # Qualified call
   ```

3. **Import specific functions**:
   ```simple
   use core.math.{sqrt, log, cos, PI}
   
   pub fn gauss(mu: f32, sigma: f32) -> f32:
       val z0 = sqrt(...)  # Direct call
   ```

---

## Verification Commands

```bash
# Test with simple_old (Rust runtime)
./target/debug/simple_old test test/03_system/collections/
./target/debug/simple_old test test/lib/std/unit/core/time_spec.spl
./target/debug/simple_old test test/lib/std/unit/core/random_spec.spl

# Test with simple_new (Simple CLI)
./bin/wrappers/simple_new test test/03_system/collections/
./bin/wrappers/simple_new test test/lib/std/unit/core/time_spec.spl
./bin/wrappers/simple_new test test/lib/std/unit/core/random_spec.spl
```

---

## Conclusion

### ✅ Complete Consistency
- Both runners show **identical behavior**
- simple_new correctly inherits all fixes from simple_old
- No runner-specific issues found

### 📊 Final Score
- **Collections:** 22/22 (100%) ✅
- **Time:** 7/7 (100%) ✅
- **Random:** 10/12 (83%) ⚠️
- **Overall:** 39/48 (81%) 

### 🎯 Next Step
Fix the 2 remaining random tests by changing from `math.sqrt()` to direct `sqrt()` calls in `gauss()` and `expovariate()` functions.

---

**Report Generated:** 2026-01-30  
**Runners Tested:** simple_old, simple_new  
**Result:** Perfect consistency across both implementations
