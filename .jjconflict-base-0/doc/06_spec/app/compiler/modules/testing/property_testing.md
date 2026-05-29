# Property-Based Testing Specification (#894-898)

**Status:** 📋 Planned  
**Category:** LLM-Friendly Features  
**Priority:** Medium  
**Difficulty:** 3-4

## Overview

Property-based testing framework that generates random inputs to verify invariant properties hold for all possible values, catching edge cases that LLMs typically miss.

## Features

### #894: `@property_test` Decorator (Difficulty: 3)

**Syntax:**
```simple
@property_test
@property_test(iterations: N)
@property_test(seed: N, iterations: M)
fn test_property(arg1: Type1, arg2: Type2):
    # Test body with assertions
```

**Implementation:**
- Parser support for decorator with optional parameters
- Runtime framework to generate inputs and run iterations
- Failure reporting with minimal failing example

**Test Execution:**
1. Generate random input for each parameter type
2. Run test function with generated inputs
3. Repeat for N iterations (default: 100)
4. On failure, trigger shrinking to find minimal case

### #895: Input Generators (Difficulty: 3)

**Built-in Generators:**
```simple
# Primitive types
gen.i64()          # Random integers
gen.i64_range(0, 100)  # In range
gen.f64()          # Floats
gen.bool()         # True/False
gen.string()       # Random strings
gen.string_alpha() # Alphabetic only

# Collections
gen.array(element_gen, size)  # Arrays
gen.array_range(gen, 0, 10)   # Variable size
gen.dict(key_gen, val_gen)    # Dictionaries
gen.optional(gen)             # Optional values

# Complex types
gen.tuple(gen1, gen2, ...)    # Tuples
gen.choice([val1, val2, ...]) # Pick from list
gen.weighted([(gen1, 0.7), (gen2, 0.3)])  # Weighted choice
```

**Custom Generators:**
```simple
# Define custom generator
fn gen_user() -> User:
    return User(
        id: gen.i64_range(1, 1000000),
        name: gen.string_alpha(),
        age: gen.i64_range(0, 120)
    )

@property_test
fn test_user_serialization(user: User):
    user = gen_user()
    let json = to_json(user)
    let deserialized = from_json(json, User)
    expect(deserialized).to_equal(user)
```

**Implementation Location:** `simple/std_lib/src/testing/property/generators.spl`

### #896: Shrinking on Failure (Difficulty: 4)

**Algorithm:**
1. When test fails with input X, try simpler variants
2. Binary search on collections (reduce size)
3. Simplify numbers (move toward 0)
4. Simplify strings (remove characters)
5. Report minimal failing case

**Example Output:**
```
Property test failed after 734 iterations
Original failing input: [47, -8293, 0, 12, 999, -34, 67, 1, -2, 44]
Shrunk to minimal: [0, -1]

Assertion failed: expect(sort(input)).to_be_sorted()
  Input: [0, -1]
  Got:   [0, -1]
  Expected: sorted array
```

**Implementation:**
- Shrink strategies for each type
- Configurable shrink depth
- Timeout protection (max shrink attempts)

### #897: Configurable Iterations (Difficulty: 2)

**CLI Flags:**
```bash
simple test --property-iterations=1000    # Override default
simple test --property-seed=42            # Reproducible tests
simple test --property-max-shrinks=100    # Shrink limit
```

**In-test Configuration:**
```simple
@property_test(
    iterations: 10000,
    seed: 42,
    max_shrinks: 50,
    timeout: 60.0  # seconds
)
fn test_expensive_property():
    ...
```

**Environment Variables:**
```bash
SIMPLE_PROPERTY_ITERATIONS=1000
SIMPLE_PROPERTY_SEED=42
```

### #898: Generator Combinators (Difficulty: 3)

**Combinators:**
```simple
# Map: transform generated values
gen.map(gen.i64(), |x| x * 2)

# Filter: only accept certain values
gen.filter(gen.i64(), |x| x > 0)

# FlatMap: dependent generation
gen.flat_map(gen.i64_range(1, 10), |size|
    gen.array(gen.i64(), size)
)

# Chain: combine generators sequentially
gen.chain([
    gen.constant(0),
    gen.i64_range(1, 10),
    gen.i64_range(100, 1000)
])

# Frequency: weighted random choice
gen.frequency([
    (8, gen.i64_range(0, 100)),      # 80% small numbers
    (2, gen.i64_range(1000, 10000))  # 20% large numbers
])

# One of: pick uniformly from generators
gen.one_of([gen.i64(), gen.f64_as_i64(), gen.constant(0)])
```

**Example Usage:**
```simple
# Generate sorted arrays
let sorted_array_gen = gen.flat_map(
    gen.i64_range(0, 20),  # Size
    |size| gen.array(gen.i64(), size)
).map(|arr| sort(arr))

@property_test
fn test_sorted_stays_sorted(arr: [i64]):
    arr = sorted_array_gen()
    expect(sort(arr)).to_equal(arr)
```

## Benefits for LLM Tools

1. **Edge Case Discovery** - Catches cases LLMs forget
2. **Specification Verification** - Tests properties, not examples
3. **Minimal Failures** - Shrinking shows simplest failing case
4. **Reproducibility** - Seed parameter for consistent runs
5. **Confidence** - 1000s of test cases vs handful of examples

## Implementation Plan

### Phase 1: Core Framework (2 days)
- [ ] Parser support for `@property_test` decorator
- [ ] Basic generator framework in stdlib
- [ ] Primitive type generators (int, bool, string)
- [ ] Test runner integration
- [ ] Simple failure reporting

### Phase 2: Generators & Combinators (2 days)
- [ ] Collection generators (array, dict, tuple)
- [ ] Generator combinators (map, filter, flatMap)
- [ ] Custom generator registration
- [ ] Weighted/frequency generators
- [ ] Range and choice generators

### Phase 3: Shrinking (3 days)
- [ ] Shrink strategies for primitives
- [ ] Shrink strategies for collections
- [ ] Shrink orchestrator (binary search)
- [ ] Minimal failure detection
- [ ] Shrink timeout protection

### Phase 4: Configuration & CLI (1 day)
- [ ] Iteration configuration
- [ ] Seed configuration for reproducibility
- [ ] CLI flags for property tests
- [ ] Environment variable support
- [ ] Test report formatting

### Phase 5: Documentation & Examples (1 day)
- [ ] User guide with examples
- [ ] API documentation
- [ ] Common patterns guide
- [ ] Migration from example-based tests
- [ ] Performance tuning guide

**Total Estimated Effort:** 9 days

## File Structure

```
simple/std_lib/src/testing/property/
├── __init__.spl           # Main exports
├── decorator.spl          # @property_test implementation
├── generators.spl         # Built-in generators
├── combinators.spl        # Generator combinators
├── shrinking.spl          # Shrink strategies
├── runner.spl             # Test execution engine
├── config.spl             # Configuration handling
└── report.spl             # Failure reporting

simple/std_lib/test/system/property/
├── generators_spec.spl    # Generator tests
├── shrinking_spec.spl     # Shrinking tests
├── combinators_spec.spl   # Combinator tests
└── integration_spec.spl   # End-to-end tests
```

## Example Use Cases

### 1. Reversibility Properties
```simple
@property_test
fn test_reverse_twice_is_identity(arr: [i64]):
    arr = gen.array(gen.i64(), gen.i64_range(0, 100))()
    expect(reverse(reverse(arr))).to_equal(arr)
```

### 2. Idempotence
```simple
@property_test
fn test_sort_is_idempotent(arr: [i64]):
    arr = gen.array(gen.i64(), 20)()
    expect(sort(sort(arr))).to_equal(sort(arr))
```

### 3. Invariants
```simple
@property_test
fn test_set_add_contains(value: i64):
    value = gen.i64()()
    let s = Set.new()
    s.add(value)
    expect(s.contains(value)).to_be_true()
```

### 4. Round-trip Encoding
```simple
@property_test
fn test_json_roundtrip(user: User):
    user = gen_user()
    let json = to_json(user)
    let decoded = from_json(json, User)
    expect(decoded).to_equal(user)
```

### 5. Comparison Operators
```simple
@property_test
fn test_comparison_transitivity(a: i64, b: i64, c: i64):
    [a, b, c] = [gen.i64()(), gen.i64()(), gen.i64()()]
    if a < b and b < c:
        expect(a < c).to_be_true()
```

## Related Features

- #300-301: BDD Spec framework (already complete)
- #899-902: Snapshot testing (complementary)
- #916-919: Sandboxed execution (safety)

## Success Metrics

- [ ] 100+ property tests in stdlib
- [ ] Catches 80%+ edge cases in test suite
- [ ] Shrinking reduces failures to <10 elements
- [ ] LLM-generated code passes property tests
- [ ] 95%+ developer satisfaction

## References

- **QuickCheck** (Haskell) - Original property testing framework
- **Hypothesis** (Python) - Modern property testing with shrinking
- **PropEr** (Erlang) - Concurrent property testing
- **FsCheck** (F#) - .NET property testing
- **fast-check** (JavaScript) - JS property testing

---

**Next Steps:**
1. Review and approve specification
2. Implement Phase 1 (core framework)
3. Add to feature.md as complete when done
4. Update LLM feature progress
