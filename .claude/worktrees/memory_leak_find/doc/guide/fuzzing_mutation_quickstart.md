# Fuzzing and Mutation Testing Quick Start

**Last Updated:** 2026-01-21
**Status:** Prototype (Fuzzing), Planned (Mutation Testing)

## Overview

Simple provides two testing tools written in Simple:

1. **`std.testing.fuzz`** - Property-based fuzzing (✅ Implemented)
2. **`std.testing.mutate`** - Mutation testing (⏳ Planned)

## 1. Property-Based Fuzzing

### What is Property-Based Testing?

Instead of writing individual test cases, you write **properties** that should always hold:

```simple
# Example-based (traditional)
describe "String reverse":
    it "reverses 'hello'":
        expect "hello".reverse() == "olleh"
    it "reverses 'world'":
        expect "world".reverse() == "dlrow"

# Property-based (fuzzing)
describe "String reverse":
    it "is involution (reverse twice = original)":
        fn prop(s: text) -> bool:
            s.reverse().reverse() == s

        val result = fuzz.fuzz(prop, fuzz.text(0, 100), 1000)
        expect result.is_pass()
```

The fuzzer automatically generates 1000 random strings and tests the property.

### Installation

Already included in stdlib:

```simple
import std.testing.fuzz as fuzz
```

### Basic Usage

**Step 1: Write a property**

```simple
fn prop_addition_commutative(x: i32) -> bool:
    val y = x + 1
    x + y == y + x
```

**Step 2: Choose a generator**

```simple
val gen = fuzz.int(-1000, 1000)  # Integers from -1000 to 1000
```

**Step 3: Run the fuzzer**

```simple
val result = fuzz.fuzz(prop_addition_commutative, gen, 100)
expect result.is_pass()
```

### Available Generators

| Generator | Usage | Example Values |
|-----------|-------|----------------|
| `fuzz.int(min, max)` | Integers in range | `-10, 0, 42, 100` |
| `fuzz.text(min_len, max_len)` | Random strings | `"abc", "x", "test123"` |
| `fuzz.bool()` | Random booleans | `true, false` |
| `fuzz.list(gen, min, max)` | Lists of elements | `[1, 2], [], [5, 3, 7]` |

### Common Properties

**Math Properties:**
```simple
# Commutative
fn prop_add_commutative(a: i32, b: i32) -> bool:
    a + b == b + a

# Associative
fn prop_mul_associative(a: i32, b: i32, c: i32) -> bool:
    (a * b) * c == a * (b * c)

# Identity
fn prop_add_zero(x: i32) -> bool:
    x + 0 == x and 0 + x == x
```

**String Properties:**
```simple
# Length preservation
fn prop_concat_length(s1: text, s2: text) -> bool:
    (s1 + s2).len() == s1.len() + s2.len()

# Reverse involution
fn prop_reverse(s: text) -> bool:
    s.reverse().reverse() == s

# Uppercase idempotent
fn prop_uppercase(s: text) -> bool:
    s.uppercase().uppercase() == s.uppercase()
```

**List Properties:**
```simple
# Append length
fn prop_append_length(xs: List, x: any) -> bool:
    val original_len = xs.len()
    xs.append(x)
    xs.len() == original_len + 1

# Sort idempotent
fn prop_sort(xs: List<i32>) -> bool:
    xs.sort().sort() == xs.sort()

# Filter count
fn prop_filter(xs: List<i32>) -> bool:
    val filtered = xs.filter(\x: x > 0)
    filtered.len() <= xs.len()
```

### Complete Example

```simple
# file: test/calculator_fuzz_spec.spl
"""
# Calculator Fuzzing Tests

Property-based tests for calculator functions.
"""

import std.spec
import std.testing.fuzz as fuzz

# Function under test
fn divide(a: i32, b: i32) -> Result<f64, text>:
    if b == 0:
        return Err("Division by zero")
    Ok((a as f64) / (b as f64))

describe "Calculator fuzzing":
    context "Division properties":
        it "never divides by zero":
            fn prop(b: i32) -> bool:
                val result = divide(100, b)
                if b == 0:
                    result.is_err()
                else:
                    result.is_ok()

            val gen = fuzz.int(-100, 100)
            val result = fuzz.fuzz(prop, gen, 500)
            expect result.is_pass()

        it "satisfies multiplication inverse":
            fn prop(a: i32) -> bool:
                val b = 5  # Non-zero divisor
                val result = divide(a, b)
                if result.is_err():
                    return false

                val quotient = result.unwrap()
                val reconstructed = (quotient * (b as f64)) as i32
                # Allow small rounding error
                (reconstructed - a).abs() <= 1

            val gen = fuzz.int(-1000, 1000)
            val result = fuzz.fuzz(prop, gen, 200)
            expect result.is_pass()

    context "List operations":
        it "append never loses elements":
            fn prop(xs: List<i32>) -> bool:
                val original_len = xs.len()
                val x = 42
                xs.append(x)
                xs.len() == original_len + 1 and xs[xs.len() - 1] == x

            val gen = fuzz.list(fuzz.int(0, 100), 0, 20)
            val result = fuzz.fuzz(prop, gen, 200)
            expect result.is_pass()
```

### Running Fuzzing Tests

```bash
# Run all tests (including fuzz tests)
simple test

# Run specific fuzz spec
simple test test/calculator_fuzz_spec.spl

# Run with more iterations (via environment variable)
FUZZ_ITERATIONS=10000 simple test
```

### Tips

**1. Start with small iteration counts (100-500)**
- Fuzzing can be slow for complex properties
- Increase gradually if no bugs found

**2. Use meaningful property names**
```simple
# Good
fn prop_reverse_involution(s: text) -> bool

# Bad
fn prop1(s: text) -> bool
```

**3. Handle edge cases**
```simple
fn prop_division(a: i32, b: i32) -> bool:
    if b == 0:
        return true  # Skip division by zero
    # ... test property
```

**4. Keep properties simple**
```simple
# Too complex
fn prop_complex(xs: List) -> bool:
    xs.map(\x: x * 2).filter(\x: x > 10).len() <= xs.len() * 0.5

# Better - split into multiple properties
fn prop_map_preserves_length(xs: List) -> bool:
    xs.map(\x: x * 2).len() == xs.len()

fn prop_filter_reduces_size(xs: List) -> bool:
    xs.filter(\x: x > 10).len() <= xs.len()
```

## 2. Mutation Testing (Coming Soon)

### What is Mutation Testing?

Mutation testing validates test quality by injecting bugs:

```simple
# Original code
fn abs(x: i32) -> i32:
    if x < 0:      # ← Mutate to: if x <= 0
        return -x
    else:
        return x
```

If your tests still pass with the mutant, they're **weak**.

### Planned API

```simple
import std.testing.mutate as mutate

describe "Code quality":
    it "has high mutation coverage":
        val report = mutate.run(
            source: "src/calculator.spl",
            test_cmd: "simple test test/calculator_spec.spl"
        )

        print report.summary()
        # Expect 80%+ mutation score
        expect report.score() > 0.8
```

### Planned CLI

```bash
# Test single file
simple mutate src/calculator.spl

# Test with specific operators
simple mutate src/logic.spl --ops binop,cmp

# Parallel execution
simple mutate src/ --jobs 4

# Generate HTML report
simple mutate src/ --report mutants.html
```

### Status

**Blocked on:** `std.parser` API (need AST access for mutations)

**Timeline:** TBD (depends on parser refactoring)

## Comparison: Simple vs. Rust Tools

| Tool | Use For | Language | Speed | Setup |
|------|---------|----------|-------|-------|
| **std.testing.fuzz** | Testing Simple apps | Simple | Medium | `import` only |
| **cargo-fuzz** | Testing compiler | Rust | Fast | Install + nightly |
| **std.testing.mutate** | Validating Simple tests | Simple | Slow | Planned |
| **cargo-mutants** | Validating Rust tests | Rust | Fast | Install |

**Rule of thumb:**
- Testing **Simple code** → Use Simple tools
- Testing **compiler** → Use Rust tools

## Examples in Stdlib

See these specs for more examples:

- `simple/std_lib/test/unit/testing/fuzz_spec.spl` - Basic fuzzing
- `simple/std_lib/test/unit/compiler_core/list_fuzz_spec.spl` - List properties (TODO)
- `simple/std_lib/test/unit/compiler_core/string_fuzz_spec.spl` - String properties (TODO)

## Further Reading

- [Design Document](../research/simple_fuzzing_mutation_design.md) - Full design
- [Rust Tools Research](../research/fuzzing_mutation_testing_2026.md) - Rust ecosystem
- [SSpec Guide](.claude/skills/sspec.md) - Writing specs
- [QuickCheck Paper](https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf) - Original property testing
- [Property-Based Testing Book](https://www.fuzzingbook.org/html/GreyboxFuzzer.html) - Theory

## Contributing

**To improve fuzzing:**
1. Add more generators (e.g., `tuple`, `dict`, `custom`)
2. Implement shrinking (minimize failing inputs)
3. Add coverage tracking
4. Improve performance

**To help with mutation testing:**
1. Contribute to `std.parser` API
2. Design mutation operators
3. Implement parallel execution
4. Create HTML report templates

---

**Questions?** See `simple/bug_report.md` or `simple/improve_request.md`
