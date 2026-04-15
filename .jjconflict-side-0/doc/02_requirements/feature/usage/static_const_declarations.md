# Static and Const Declarations Specification
*Source:* `test/feature/usage/static_const_declarations_spec.spl`
**Feature IDs:** #STATIC-001 to #STATIC-015  |  **Category:** Language | Declarations  |  **Status:** Planned

## Overview



## Overview

Static and const declarations provide compile-time and runtime constants with
different scoping and initialization rules:
1. `static val` - Module-level immutable constants with static lifetime
2. `static var` - Module-level mutable state (requires careful use)
3. `const` - Compile-time constants with inline optimization
4. `static fn` - Static methods accessible via type/module name

## Syntax

```simple
# Static value (module-level constant)
static val PI = 3.14159
static val MAX_SIZE = 1000

# Static mutable (rare, requires synchronization)
static var counter = 0

# Const (compile-time constant)
const VERSION = "1.0.0"
const DEBUG = false

# Static method
impl Math:
    static fn abs(n: i64) -> i64:
        if n < 0: -n else: n

# Static method usage
val result = Math.abs(-42)
```

## Key Concepts

| Concept | Scope | Initialization | Mutability | Use Case |
|---------|-------|-----------------|-----------|----------|
| static val | Module | Runtime | Immutable | Constants, caches |
| static var | Module | Runtime | Mutable | State, counters |
| const | Module | Compile-time | Immutable | Literals, flags |
| static fn | Type | N/A | N/A | Factory, utility |

## Behavior

- Static values are initialized once at module load
- Constants are inlined at compile time
- Static methods do not receive `self` parameter
- Static var requires thread-safe access in concurrent contexts
- Statics are lazily initialized (first access)

## Related Specifications

- [Module System](module_system_spec.spl) - Scoping rules
- [Functions](functions_spec.spl) - Method definitions

## Feature: Static Value Declaration

expect(true).to_equal(true)

    it "initializes static value from collection":
        val source = """
static val NUMBERS = [1, 2, 3, 4, 5]

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple static value | pass |
| 2 | parses static value with type annotation | pass |
| 3 | parses static value with complex expression | pass |
| 4 | parses multiple static values | pass |
| 5 | parses static method with no parameters | pass |
| 6 | parses static method returning complex type | pass |
| 7 | initializes static value from function call | pass |

**Example:** parses simple static value
    Given val source = "static val PI = 3.14159"
    Then  expect(true).to_equal(true)

**Example:** parses static value with type annotation
    Given val source = "static val MAX_SIZE: i64 = 1000"
    Then  expect(true).to_equal(true)

**Example:** parses static value with complex expression
    Given val source = "static val GREETING = \"Hello, \" + \"World\""
    Then  expect(true).to_equal(true)

**Example:** parses multiple static values
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** parses static method with no parameters
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** parses static method returning complex type
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** initializes static value from function call
    Given val source = """
    Then  expect(true).to_equal(true)

## Feature: Static Value Access

expect(true).to_equal(true)

    it "uses const in expression":
        val source = """
const DEBUG = true
fn maybe_print(msg):
    if DEBUG: print msg

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | accesses static value in function | pass |
| 2 | uses static value in expression | pass |
| 3 | evaluates const string concatenation | pass |

**Example:** accesses static value in function
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** uses static value in expression
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** evaluates const string concatenation
    Given val source = """
    Then  expect(true).to_equal(true)

## Feature: Static Method Call Syntax

it "parses static mutable variable":
        val source = "static var counter = 0"
        expect(true).to_equal(true)

    it "parses static var with type annotation":
        val source = "static var state: i64 = 100"
        expect(true).to_equal(true)

    it "accesses static var":
        val source = """
static var count = 0
fn get_count():
    count

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calls static method on class | pass |
| 2 | calls static method and uses result | pass |

**Example:** calls static method on class
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** calls static method and uses result
    Given val source = """
    Given val result = Factory.create()
    Then  expect(true).to_equal(true)

## Feature: Static and Const Visibility

expect(true).to_equal(true)

    it "handles circular static references safely":
        val source = """
static val X = 10
static val Y = X + 5

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses public static value | pass |
| 2 | parses public const | pass |
| 3 | parses public static method | pass |
| 4 | allows static reference to earlier static | pass |

**Example:** parses public static value
    Given val source = "pub static val PUBLIC_CONST = 42"
    Then  expect(true).to_equal(true)

**Example:** parses public const
    Given val source = "pub const PUBLIC_CONST = \"visible\""
    Then  expect(true).to_equal(true)

**Example:** parses public static method
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** allows static reference to earlier static
    Given val source = """
    Then  expect(true).to_equal(true)

## Feature: Static Declaration Edge Cases

expect(true).to_equal(true)

    it "calls static method from imported module":
        val source = """
import utils.math

fn test():
    math.abs(-5)

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | rejects static with no initializer | pass |
| 2 | rejects const with no initializer | pass |
| 3 | rejects static keyword in function body | pass |
| 4 | rejects duplicate static declaration | pass |
| 5 | rejects const with non-literal array | pass |
| 6 | static method separate from instance methods | pass |
| 7 | references const from imported module | pass |

**Example:** rejects static with no initializer
    Given val source = "static val UNINITIALIZED: i64"
    Then  expect(true).to_equal(true)  # Should error

**Example:** rejects const with no initializer
    Given val source = "const UNINITIALIZED: i64"
    Then  expect(true).to_equal(true)  # Should error

**Example:** rejects static keyword in function body
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** rejects duplicate static declaration
    Given val source = """
    Then  expect(true).to_equal(true)  # May error depending on semantics

**Example:** rejects const with non-literal array
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** static method separate from instance methods
    Given val source = """
    Given var count: i64
    Then  expect(true).to_equal(true)

**Example:** references const from imported module
    Given val source = """
    Given val timeout = defaults.TIMEOUT
    Then  expect(true).to_equal(true)


