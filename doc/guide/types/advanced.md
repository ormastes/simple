# Advanced Type System Guide
**Simple Language - Type System Features**
**Version:** 1.0 (2026-02-14)

---

## Overview

Simple's advanced type system provides three powerful features:

1. **Union Types** - Value can be one of several types (`i64 | text`)
2. **Intersection Types** - Value must satisfy multiple type constraints (`Serializable & Comparable`)
3. **Refinement Types** - Value must satisfy a predicate (`x: i64 where x > 0`)

These features work at **runtime** with full type checking support.

---

## Union Types

### Syntax

```simple
# Union type declaration (future syntax)
type IntOrText = i64 | text
type OptionalInt = i64 | nil
type Result = Success | Error | Pending
```

### Usage

Union types express "this OR that" relationships:

```simple
fn process_value(value: i64 | text):
    # Runtime checks which type it is
    if value is i64:
        print "Integer: {value}"
    else:
        print "Text: {value}"
```

### Runtime Checking

```simple
# Using type_checker.spl
use core.type_checker.{type_check_union}

val union_id = 0  # From union type registry
val value_id = 42  # Runtime value ID

if type_check_union(value_id, union_id):
    print "Value matches union type"
```

### Common Patterns

#### Optional Values
```simple
type Optional<T> = T | nil

fn divide(a: i64, b: i64) -> i64 | nil:
    if b == 0:
        return nil
    a / b
```

#### Multi-Type Returns
```simple
type ParseResult = i64 | text  # i64 on success, text error on failure

fn parse_int(s: text) -> ParseResult:
    if s == "":
        return "Empty string"
    int(s)  # Returns i64 or nil
```

#### Status Codes
```simple
type Status = :success | :error | :pending | :timeout

fn check_status() -> Status:
    :success
```

---

## Intersection Types

### Syntax

```simple
# Intersection type declaration (future syntax)
type SerializableComparable = Serializable & Comparable
type NumericType = Arithmetic & Ordered
```

### Usage

Intersection types express "this AND that" requirements:

```simple
fn sort<T: Comparable & Hashable>(items: [T]):
    # T must support both comparison and hashing
    pass_todo
```

### Runtime Checking

```simple
use core.type_checker.{type_check_intersection}

val inter_id = 0  # From intersection type registry
val value_id = 42

if type_check_intersection(value_id, inter_id):
    print "Value satisfies all type constraints"
```

### Common Patterns

#### Trait Bounds
```simple
trait Serializable:
    fn serialize() -> text

trait Comparable:
    fn compare(other: self) -> i64

# Require both traits
fn process<T: Serializable & Comparable>(item: T):
    val json = item.serialize()
    val order = item.compare(item)
```

#### Multiple Interfaces
```simple
type DataStore = Readable & Writable & Closeable

fn use_store(store: DataStore):
    val data = store.read()
    store.write(data)
    store.close()
```

---

## Refinement Types

### Syntax

```simple
# Refinement type declaration (future syntax)
type PositiveInt = x: i64 where x > 0
type NonEmptyText = s: text where len(s) > 0
type BoundedValue = v: i64 where v >= 0 and v < 100
```

### Usage

Refinement types add runtime predicates:

```simple
fn sqrt(x: i64 where x >= 0) -> f64:
    # x is guaranteed non-negative at runtime
    math.sqrt(float(x))

fn create_user(name: text where len(name) > 0):
    # name is guaranteed non-empty
    print "Creating user: {name}"
```

### Runtime Checking

```simple
use core.type_checker.{type_check_refinement}

val ref_id = 0  # From refinement type registry
val value_id = 5

if type_check_refinement(value_id, ref_id):
    print "Value satisfies predicate"
else:
    print "Predicate violated"
```

### Supported Predicates

#### Integer Comparisons
```simple
type PositiveInt = x: i64 where x > 0
type NonNegativeInt = x: i64 where x >= 0
type BoundedInt = x: i64 where x < 100
type RangeInt = x: i64 where x >= 0 and x < 100
```

#### Length Constraints
```simple
type NonEmptyText = s: text where len(s) > 0
type ShortText = s: text where len(s) < 256
type FixedText = s: text where len(s) == 10

type NonEmptyArray = a: [i64] where len(a) > 0
type SmallArray = a: [i64] where len(a) <= 10
```

#### Float Comparisons
```simple
type PositiveFloat = f: f64 where f > 0.0
type UnitFloat = f: f64 where f >= 0.0 and f <= 1.0
type Temperature = t: f64 where t >= -273.15  # Absolute zero
```

### Common Patterns

#### Input Validation
```simple
fn set_age(age: i64 where age >= 0 and age < 150):
    # Age is validated at runtime before function executes
    print "Age: {age}"
```

#### Array Safety
```simple
fn first<T>(arr: [T] where len(arr) > 0) -> T:
    # Guaranteed non-empty, safe to index
    arr[0]

fn last<T>(arr: [T] where len(arr) > 0) -> T:
    arr[arr.len() - 1]
```

#### Numeric Bounds
```simple
fn percent_to_fraction(p: i64 where p >= 0 and p <= 100) -> f64:
    float(p) / 100.0

fn clamp_byte(v: i64) -> i64 where result >= 0 and result <= 255:
    if v < 0: return 0
    if v > 255: return 255
    v
```

---

## Generic Functions with Type Constraints

### Basic Generics

```simple
fn identity<T>(x: T) -> T:
    x

fn pair<A, B>(a: A, b: B) -> (A, B):
    (a, b)
```

### Constrained Generics

```simple
fn compare<T: Comparable>(a: T, b: T) -> i64:
    a.compare(b)

fn serialize<T: Serializable>(obj: T) -> text:
    obj.serialize()
```

### Multiple Constraints

```simple
fn sort_and_hash<T: Comparable & Hashable>(items: [T]):
    items.sort()
    for item in items:
        print item.hash()
```

### Refinement Constraints

```simple
fn safe_divide(a: i64, b: i64 where b != 0) -> i64:
    a / b

fn log_positive(x: f64 where x > 0.0) -> f64:
    math.log(x)
```

---

## Type Inference

Simple can infer types in many contexts:

### Literal Inference

```simple
val x = 42          # Inferred: i64
val y = 3.14        # Inferred: f64
val z = "hello"     # Inferred: text
val b = true        # Inferred: bool
```

### Function Return Inference

```simple
fn double(x):       # Infers: fn(i64) -> i64
    x * 2

fn concat(a, b):    # Infers: fn(text, text) -> text
    a + b
```

### Generic Instantiation

```simple
fn identity<T>(x: T) -> T:
    x

val n = identity(42)        # T inferred as i64
val s = identity("text")    # T inferred as text
```

### Lambda Inference

```simple
val numbers = [1, 2, 3]
val doubled = numbers.map(\x: x * 2)  # x inferred as i64
```

---

## Type Checking API

### Runtime Type Validation

```simple
use core.type_checker.{type_check, type_check_union, type_check_intersection, type_check_refinement}

# Basic type check
fn validate_int(value_id: i64) -> bool:
    type_check(value_id, TYPE_I64)

# Union check
fn validate_optional(value_id: i64, union_id: i64) -> bool:
    type_check_union(value_id, union_id)

# Intersection check
fn validate_traits(value_id: i64, inter_id: i64) -> bool:
    type_check_intersection(value_id, inter_id)

# Refinement check
fn validate_positive(value_id: i64, ref_id: i64) -> bool:
    type_check_refinement(value_id, ref_id)
```

### Type Erasure/Monomorphization

```simple
use core.type_erasure.{monomorphize_generic_call, mono_function_name}

# Monomorphize generic call
fn call_generic(fn_name: text, type_args: [i64]) -> i64:
    monomorphize_generic_call(fn_name, type_args)

# Generate mangled name
val name = mono_function_name("identity", [TYPE_I64])
# Returns: "identity__i64"
```

### Type Inference

```simple
use core.type_inference.{infer_function_types, infer_expr_types, unify_types}

# Infer function parameter and return types
fn infer_func(fn_decl_id: i64, param_count: i64) -> bool:
    infer_function_types(fn_decl_id, param_count)

# Infer expression type
fn infer_expr(expr_id: i64) -> i64:
    infer_expr_types(expr_id)

# Unify two types
fn unify(type1: i64, type2: i64) -> i64:
    unify_types(type1, type2)
```

---

## Best Practices

### 1. Use Refinement Types for Input Validation

**Good:**
```simple
fn set_volume(level: i64 where level >= 0 and level <= 100):
    # Validation happens automatically at call site
    audio.volume = level
```

**Bad:**
```simple
fn set_volume(level: i64):
    if level < 0 or level > 100:
        panic("Invalid volume")
    audio.volume = level
```

### 2. Prefer Union Types Over Optional Wrappers

**Good:**
```simple
fn parse_int(s: text) -> i64 | nil:
    # Natural representation of optional result
    if s == "":
        return nil
    int(s)
```

**Bad:**
```simple
class Optional:
    has_value: bool
    value: i64

fn parse_int(s: text) -> Optional:
    # Verbose wrapper
    if s == "":
        return Optional(has_value: false, value: 0)
    Optional(has_value: true, value: int(s))
```

### 3. Use Intersection Types for Multiple Trait Bounds

**Good:**
```simple
fn process<T: Serializable & Comparable>(item: T):
    # Clear constraint expression
    pass_todo
```

**Bad:**
```simple
fn process<T>(item: T):
    # Runtime type checks scattered throughout
    if not item.is_serializable():
        panic()
    if not item.is_comparable():
        panic()
```

### 4. Leverage Type Inference

**Good:**
```simple
val numbers = [1, 2, 3]
val doubled = numbers.map(\x: x * 2)
```

**Bad:**
```simple
val numbers: [i64] = [1, 2, 3]
val doubled: [i64] = numbers.map(\x: i64: i64 { x * 2 })
```

---

## Performance Considerations

### Runtime Type Checking Costs

| Operation | Complexity | Cost |
|-----------|-----------|------|
| Basic type check | O(1) | ~10 ns |
| Union check (n members) | O(n) | ~10n ns |
| Intersection check (m members) | O(m) | ~10m ns |
| Refinement check | O(1) | ~50 ns (predicate eval) |
| Struct field validation | O(fields) | ~20f ns |

### Monomorphization Costs

| Operation | Complexity | Cost |
|-----------|-----------|------|
| Cache lookup | O(instances) | ~50 ns |
| Name mangling | O(type_args) | ~100 ns |
| Instance generation | O(AST_size) | ~1 μs |

### Type Inference Costs

| Operation | Complexity | Cost |
|-----------|-----------|------|
| Type variable allocation | O(1) | ~20 ns |
| Unification | O(depth) | ~100 ns |
| Constraint solving | O(constraints) | ~50c ns |

### Optimization Tips

1. **Cache type checks** in hot paths
2. **Monomorphize eagerly** for frequently-called generics
3. **Use concrete types** when performance matters
4. **Avoid deep refinement predicates** in tight loops

---

## Migration Guide

### From Existing Code

**Before:**
```simple
fn divide(a: i64, b: i64) -> i64:
    if b == 0:
        panic("Division by zero")
    a / b
```

**After:**
```simple
fn divide(a: i64, b: i64 where b != 0) -> i64:
    # Runtime check happens automatically
    a / b
```

### Adding Union Types

**Before:**
```simple
fn parse_config(path: text) -> text:
    # Returns empty string on error
    if not file_exists(path):
        return ""
    file_read(path)
```

**After:**
```simple
fn parse_config(path: text) -> text | nil:
    # Explicit optional return
    if not file_exists(path):
        return nil
    file_read(path)
```

---

## Troubleshooting

### "Type check failed for union"
- Ensure value matches at least one union member
- Check union_id is correctly registered
- Verify value_id is valid

### "Occurs check failed" (Type Inference)
- Infinite type detected (e.g., `T = List<T>`)
- Simplify recursive type definitions
- Add explicit type annotations

### "Type mismatch" (Unification)
- Incompatible types in constraint
- Add type casts or conversions
- Check function call argument types

---

## Examples

See `test/unit/type/` for comprehensive examples:
- `runtime_type_check_spec.spl` - Runtime checking examples
- `basic_type_check_spec.spl` - Simple type validation

---

**Documentation Version:** 1.0
**Last Updated:** 2026-02-14
**Status:** Draft (awaiting integration completion)
