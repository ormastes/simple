# Advanced Type System - Quick Reference
**Simple Language Type System Cheat Sheet**

---

## Union Types (OR)

```simple
# Value can be ONE of several types
type Result = i64 | text         # Integer OR text
type Optional = T | nil          # Value OR nil
type Status = :ok | :error       # Symbol variants
```

**Usage:**
```simple
fn parse(s: text) -> i64 | nil:
    if s == "": return nil
    int(s)

val result = parse("42")
if result is i64:
    print "Got number: {result}"
```

---

## Intersection Types (AND)

```simple
# Value must satisfy ALL types
type Comparable = trait { fn compare(other: self) -> i64 }
type Hashable = trait { fn hash() -> i64 }
type Key = Comparable & Hashable  # BOTH traits required
```

**Usage:**
```simple
fn sort<T: Comparable & Hashable>(items: [T]):
    # T must support comparison AND hashing
    items.sort()
```

---

## Refinement Types (Predicates)

```simple
# Value must satisfy a predicate
type PositiveInt = x: i64 where x > 0
type NonEmpty = s: text where len(s) > 0
type Percent = p: i64 where p >= 0 and p <= 100
```

**Supported Predicates:**
- `x > N`, `x < N`, `x >= N`, `x <= N`, `x == N`, `x != N`
- `len(x) > N`, `len(x) >= N`, `len(x) == N`

**Usage:**
```simple
fn sqrt(x: i64 where x >= 0) -> f64:
    math.sqrt(float(x))

fn first(arr: [T] where len(arr) > 0) -> T:
    arr[0]  # Safe - guaranteed non-empty
```

---

## Generic Functions

```simple
# Single type parameter
fn identity<T>(x: T) -> T:
    x

# Multiple type parameters
fn pair<A, B>(a: A, b: B) -> (A, B):
    (a, b)

# Constrained generics
fn compare<T: Comparable>(a: T, b: T) -> i64:
    a.compare(b)
```

**Inference:**
```simple
val n = identity(42)        # T inferred as i64
val s = identity("hello")   # T inferred as text
```

---

## Type Checking API

```simple
use core.type_checker.{type_check, type_check_union, type_check_intersection, type_check_refinement}

# Basic check
type_check(value_id, TYPE_I64)         # → bool

# Union check
type_check_union(value_id, union_id)   # → bool

# Intersection check
type_check_intersection(value_id, inter_id)  # → bool

# Refinement check
type_check_refinement(value_id, ref_id)      # → bool
```

---

## Monomorphization API

```simple
use core.type_erasure.{monomorphize_generic_call, mono_function_name}

# Specialize generic function
val instance = monomorphize_generic_call("identity", [TYPE_I64])

# Generate mangled name
val name = mono_function_name("identity", [TYPE_I64])
# Returns: "identity__i64"
```

---

## Type Inference API

```simple
use core.type_inference.{infer_function_types, infer_expr_types, unify_types}

# Infer function types
infer_function_types(fn_decl_id, param_count)  # → bool

# Infer expression type
infer_expr_types(expr_id)                      # → i64 (type_tag)

# Unify two types
unify_types(type1, type2)                      # → result code
```

---

## Type Constants

```simple
TYPE_VOID          = 0
TYPE_BOOL          = 1
TYPE_I64           = 2
TYPE_F64           = 3
TYPE_TEXT          = 4
TYPE_ARRAY_ANY     = 8
TYPE_STRUCT        = 10
TYPE_FN            = 11
TYPE_ANY           = 12
TYPE_NIL           = 13
TYPE_UNION         = 24
TYPE_INTERSECTION  = 25
TYPE_REFINEMENT    = 26
TYPE_NAMED_BASE    = 1000  # Custom types start here
TYPE_VAR_BASE      = 50000 # Type variables start here
```

---

## Common Patterns

### Optional Values
```simple
fn divide(a: i64, b: i64) -> i64 | nil:
    if b == 0: return nil
    a / b
```

### Input Validation
```simple
fn set_age(age: i64 where age >= 0 and age < 150):
    # Age validated automatically at call site
    print "Age: {age}"
```

### Array Safety
```simple
fn first<T>(arr: [T] where len(arr) > 0) -> T:
    arr[0]  # Safe - guaranteed non-empty
```

### Multi-Constraint Generics
```simple
fn process<T: Serializable & Comparable>(item: T):
    val json = item.serialize()
    val cmp = item.compare(item)
```

---

## Performance Notes

| Operation | Complexity | Typical Cost |
|-----------|-----------|--------------|
| Basic type check | O(1) | ~10 ns |
| Union (n members) | O(n) | ~10n ns |
| Intersection (m members) | O(m) | ~10m ns |
| Refinement | O(1) | ~50 ns |
| Cache lookup | O(instances) | ~50 ns |
| Unification | O(depth) | ~100 ns |

---

## Error Codes (Type Inference)

```simple
UNIFY_SUCCESS        = 0  # Unification succeeded
UNIFY_FAIL_MISMATCH  = 1  # Incompatible types
UNIFY_FAIL_OCCURS    = 2  # Infinite type detected
```

---

## Best Practices

✅ **DO:**
- Use refinement types for input validation
- Prefer union types over Optional wrappers
- Leverage type inference where possible
- Cache type checks in hot paths

❌ **DON'T:**
- Use deep refinement predicates in loops
- Over-constrain generic type parameters
- Ignore type inference errors
- Mix concrete and inferred types unnecessarily

---

## Examples

See full examples in:
- `doc/guide/advanced_types.md` - Complete user guide
- `test/unit/type/` - Test suite examples
- `doc/report/advanced_type_system_implementation_2026-02-14.md` - Implementation details

---

**Version:** 1.0 (2026-02-14)
**Status:** Core implementation complete
