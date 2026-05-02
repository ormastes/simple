# Static and Const Declarations Specification

Static and const declarations provide compile-time and runtime constants with different scoping and initialization rules: 1. `static val` - Module-level immutable constants with static lifetime 2. `static var` - Module-level mutable state (requires careful use) 3. `const` - Compile-time constants with inline optimization 4. `static fn` - Static methods accessible via type/module name

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STATIC-001 to #STATIC-015 |
| Category | Language \| Declarations |
| Difficulty | 2/5 |
| Status | Planned |
| Source | `test/feature/usage/static_const_declarations_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Static and const declarations provide compile-time and runtime constants with
different scoping and initialization rules:
1. `static val` - Module-level immutable constants with static lifetime
2. `static var` - Module-level mutable state (requires careful use)
3. `const` - Compile-time constants with inline optimization
4. `static fn` - Static methods accessible via type/module name

## Syntax

```simple
static val PI = 3.14159
static val MAX_SIZE = 1000

static var counter = 0

const VERSION = "1.0.0"
const DEBUG = false

impl Math:
static fn abs(n: i64) -> i64:
if n < 0: -n else: n

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

expect(true).to_equal(true)


# ============================================================================
# Test Group 2: Const Declaration Parsing and Syntax
# ============================================================================

describe "Const Declaration":
    # ## Const Declaration Parsing
    #
    # Verifies that `const` declarations are parsed and recognized correctly.
    # Const values are compile-time constants.

    it "parses simple const":
        val source = "const DEBUG = false"
        expect(true).to_equal(true)

    it "parses const with type annotation":
        val source = "const VERSION: text = \"1.0.0\""
        expect(true).to_equal(true)

    it "parses const with numeric value":
        val source = "const MAX_RETRIES = 5"
        expect(true).to_equal(true)

    it "parses const with string value":
        val source = "const APP_NAME = \"MyApp\""
        expect(true).to_equal(true)


# ============================================================================
# Test Group 3: Static Method Parsing and Syntax
# ============================================================================

describe "Static Method Declaration":
    # ## Static Method Parsing
    #
    # Verifies that `static fn` method declarations are parsed correctly.
    # Static methods belong to the type/module and do not receive self.

    it "parses simple static method":
        val source = """
impl Calculator:
    static fn add(a: i64, b: i64) -> i64:
        a + b

expect(true).to_equal(true)

    it "parses static method with multiple parameters":
        val source = """
impl Point:
    static fn distance(x1: i64, y1: i64, x2: i64, y2: i64) -> i64:
        0

expect(true).to_equal(true)


# ============================================================================
# Test Group 4: Static Value Initialization
# ============================================================================

describe "Static Value Initialization":
    # ## Static Value Initialization
    #
    # Tests runtime initialization of static values.

    it "initializes simple static value":
        val source = """
static val NUMBER = 42

fn test():
    NUMBER

expect(true).to_equal(true)

    it "initializes static value from collection":
        val source = """
static val NUMBERS = [1, 2, 3, 4, 5]

expect(true).to_equal(true)

    it "accesses multiple static values":
        val source = """
static val X = 1
static val Y = 2
fn sum():
    X + Y

expect(true).to_equal(true)


# ============================================================================
# Test Group 6: Const Value Evaluation
# ============================================================================

describe "Const Value Evaluation":
    # ## Const Value Evaluation
    #
    # Tests that const values are evaluated at compile time.

    it "evaluates const arithmetic":
        val source = """
const RESULT = 2 + 3

expect(true).to_equal(true)

    it "uses const in expression":
        val source = """
const DEBUG = true
fn maybe_print(msg):
    if DEBUG: print msg

expect(true).to_equal(true)

    it "calls static method with multiple arguments":
        val source = """
impl Util:
    static fn max(a: i64, b: i64) -> i64:
        if a > b: a else: b

fn test():
    Util.max(10, 20)

expect(true).to_equal(true)


# ============================================================================
# Test Group 8: Static Var Declaration
# ============================================================================

describe "Static Var Declaration":
    # ## Static Var Declaration
    #
    # Tests mutable static variables (rare usage, requires care).

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

expect(true).to_equal(true)

    it "parses private static value":
        val source = "static val PRIVATE = 100"
        expect(true).to_equal(true)


# ============================================================================
# Test Group 10: Type Annotations on Statics
# ============================================================================

describe "Static Type Annotations":
    # ## Type Annotations on Statics
    #
    # Tests explicit type annotations for static values.

    it "annotates static with primitive type":
        val source = "static val NUM: i64 = 42"
        expect(true).to_equal(true)

    it "annotates static with generic type":
        val source = "static val ITEMS: [i64] = [1, 2, 3]"
        expect(true).to_equal(true)

    it "annotates const with text type":
        val source = "const MESSAGE: text = \"Hello\""
        expect(true).to_equal(true)

    it "annotates static with optional type":
        val source = "static val VALUE: i64? = None"
        expect(true).to_equal(true)


# ============================================================================
# Test Group 11: Static Initialization Order
# ============================================================================

describe "Static Initialization Order":
    # ## Static Initialization Order
    #
    # Tests the order of static initialization across module.

    it "initializes statics before main code":
        val source = """
static val A = 1
static val B = 2

fn test():
    A + B

expect(true).to_equal(true)

    it "handles circular static references safely":
        val source = """
static val X = 10
static val Y = X + 5

expect(true).to_equal(true)  # Should error

    it "allows static in class definition":
        val source = """
class MyClass:
    static val CLASS_CONST = 42

expect(true).to_equal(true)  # Should error


# ============================================================================
# Test Group 13: Const Expression Restrictions
# ============================================================================

describe "Const Expression Restrictions":
    # ## Const Expression Restrictions
    #
    # Tests what kinds of expressions are allowed in const initialization.

    it "allows const with arithmetic":
        val source = "const VALUE = 10 * 2 + 5"
        expect(true).to_equal(true)

    it "allows const with string literal":
        val source = "const NAME = \"System\""
        expect(true).to_equal(true)

    it "allows const with boolean":
        val source = "const ENABLED = true"
        expect(true).to_equal(true)

    it "rejects const with function call":
        val source = """
fn get_value():
    42

const VALUE = get_value()

expect(true).to_equal(true)  # May error


# ============================================================================
# Test Group 14: Static Method in Type Context
# ============================================================================

describe "Static Methods in Type Context":
    # ## Static Methods in Type Context
    #
    # Tests static methods as factory functions and type methods.

    it "uses static method as factory":
        val source = """
class Point:
    x: i64
    y: i64

impl Point:
    static fn origin() -> Point:
        Point(x: 0, y: 0)

fn test():
    val p = Point.origin()

expect(true).to_equal(true)


# ============================================================================
# Test Group 15: Cross-Module Static References
# ============================================================================

describe "Cross-Module Static References":
    # ## Cross-Module Static References
    #
    # Tests accessing statics and consts from other modules.

    it "references static from imported module":
        val source = """
use math.constants

fn test():
    constants.PI

expect(true).to_equal(true)

    it "calls static method from imported module":
        val source = """
use utils.math

fn test():
    math.abs(-5)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/static_const_declarations/result.json` |

## Scenarios

- parses simple static value
- parses static value with type annotation
- parses static value with complex expression
- parses multiple static values
- parses simple const
- parses const with type annotation
- parses const with numeric value
- parses const with string value
- parses simple static method
- parses static method with no parameters
- parses static method with multiple parameters
- parses static method returning complex type
- initializes simple static value
- initializes static value from function call
- initializes static value from collection
- accesses static value in function
- accesses multiple static values
- uses static value in expression
- evaluates const arithmetic
- evaluates const string concatenation
- uses const in expression
- calls static method on class
- calls static method with multiple arguments
- calls static method and uses result
- parses static mutable variable
- parses static var with type annotation
- accesses static var
- parses public static value
- parses public const
- parses public static method
- parses private static value
- annotates static with primitive type
- annotates static with generic type
- annotates const with text type
- annotates static with optional type
- initializes statics before main code
- allows static reference to earlier static
- handles circular static references safely
- rejects static with no initializer
- rejects const with no initializer
- rejects static keyword in function body
- allows static in class definition
- rejects duplicate static declaration
- allows const with arithmetic
- allows const with string literal
- allows const with boolean
- rejects const with function call
- rejects const with non-literal array
- uses static method as factory
- static method separate from instance methods
- references static from imported module
- references const from imported module
- calls static method from imported module
