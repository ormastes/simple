# Type Registry API Reference

**Status:** ⚠️ PARTIAL IMPLEMENTATION - Registry functions exist, runtime checking NOT implemented

**Location:** `src/core/types.spl` (lines 439-581)

**Implemented:** Type registration and storage
**Not Implemented:** Runtime type checking, type erasure, type inference

---

## Overview

The Simple type system includes a registry for advanced type constructs:
- **Generic Parameters** - Type parameters for generic classes and functions
- **Union Types** - Types representing "A or B or C"
- **Intersection Types** - Types representing "A and B and C"
- **Refinement Types** - Base types with predicates (e.g., "positive integers")

Currently, these types can be **registered** but not **checked at runtime**.

---

## Generic Parameters

### `generic_param_register(name: text, context: text) -> i64`

Register a generic type parameter.

**Parameters:**
- `name` - Parameter name (e.g., "T", "K", "V")
- `context` - Context where parameter is defined (e.g., function or class name)

**Returns:** Parameter ID for later reference

**Example:**
```simple
use core.types.{generic_param_register, generic_param_find}

# Register type parameter T in context of identity function
val param_id = generic_param_register("T", "identity")
print param_id  # e.g., 0
```

---

### `generic_param_find(name: text, context: text) -> i64`

Find a previously registered generic parameter.

**Parameters:**
- `name` - Parameter name to search for
- `context` - Context to search in

**Returns:** Parameter ID, or -1 if not found

**Example:**
```simple
val param_id = generic_param_find("T", "identity")
if param_id >= 0:
    print "Found parameter: {param_id}"
else:
    print "Parameter not found"
```

---

### `generic_param_name(param_id: i64) -> text`

Get the name of a generic parameter by ID.

**Parameters:**
- `param_id` - Parameter ID from `generic_param_register()`

**Returns:** Parameter name

---

### `generic_param_context(param_id: i64) -> text`

Get the context of a generic parameter by ID.

**Parameters:**
- `param_id` - Parameter ID from `generic_param_register()`

**Returns:** Context name

---

### `generic_param_count() -> i64`

Get total number of registered generic parameters.

**Returns:** Count of parameters

---

## Union Types

A union type represents "one of several possible types". For example, `Result<T, E>` might be internally represented as a union of success and error cases.

### `union_type_register(member_types: [i64]) -> i64`

Register a union type with its member types.

**Parameters:**
- `member_types` - Array of type IDs that are valid members of this union

**Returns:** Union type ID

**Example:**
```simple
use core.types.{union_type_register, union_type_get_members}

# Register union of Int | Text | Bool (hypothetical type IDs)
val int_type = 1
val text_type = 2
val bool_type = 3
val members = [int_type, text_type, bool_type]
val union_id = union_type_register(members)

print "Union type ID: {union_id}"
```

---

### `union_type_get_members(union_id: i64) -> [i64]`

Get the member types of a union type.

**Parameters:**
- `union_id` - Union type ID from `union_type_register()`

**Returns:** Array of member type IDs, or empty array if invalid ID

**Example:**
```simple
val members = union_type_get_members(union_id)
print "Union has {members.len()} member types"
for member in members:
    print "  Member type ID: {member}"
```

---

## Intersection Types

An intersection type represents "all of these types simultaneously". This is useful for structural typing where a value must satisfy multiple interfaces.

### `intersection_type_register(member_types: [i64]) -> i64`

Register an intersection type with its member types.

**Parameters:**
- `member_types` - Array of type IDs that must ALL be satisfied

**Returns:** Intersection type ID

**Example:**
```simple
use core.types.{intersection_type_register, intersection_type_get_members}

# Register intersection of Comparable & Serializable (hypothetical)
val comparable_type = 10
val serializable_type = 11
val members = [comparable_type, serializable_type]
val inter_id = intersection_type_register(members)

print "Intersection type ID: {inter_id}"
```

---

### `intersection_type_get_members(inter_id: i64) -> [i64]`

Get the member types of an intersection type.

**Parameters:**
- `inter_id` - Intersection type ID from `intersection_type_register()`

**Returns:** Array of member type IDs, or empty array if invalid ID

---

## Refinement Types

A refinement type is a base type plus a predicate constraint. For example, "positive integers" is a refinement of the integer type.

### `refinement_type_register(base_type: i64, predicate: text) -> i64`

Register a refinement type with a base type and predicate.

**Parameters:**
- `base_type` - Base type ID (e.g., integer type)
- `predicate` - Predicate expression as text (e.g., "x > 0")

**Returns:** Refinement type ID

**Example:**
```simple
use core.types.{refinement_type_register, refinement_type_base, refinement_type_predicate}

# Register "positive integers" refinement
val int_type = 1
val predicate = "x > 0"
val pos_int_id = refinement_type_register(int_type, predicate)

print "Positive integer type ID: {pos_int_id}"
```

---

### `refinement_type_base(ref_id: i64) -> i64`

Get the base type of a refinement type.

**Parameters:**
- `ref_id` - Refinement type ID from `refinement_type_register()`

**Returns:** Base type ID, or -1 if invalid

---

### `refinement_type_predicate(ref_id: i64) -> text`

Get the predicate of a refinement type.

**Parameters:**
- `ref_id` - Refinement type ID from `refinement_type_register()`

**Returns:** Predicate text, or empty string if invalid

**Example:**
```simple
val base = refinement_type_base(pos_int_id)
val pred = refinement_type_predicate(pos_int_id)
print "Refinement of type {base} with predicate: {pred}"
```

---

## Limitations (Current Implementation)

⚠️ **These functions are NOT yet implemented:**

- `type_check_union(value: any, union_id: i64) -> bool` - Check if value matches union type
- `type_check_intersection(value: any, inter_id: i64) -> bool` - Check if value matches intersection
- `type_check_refinement(value: any, ref_id: i64) -> bool` - Check if value satisfies refinement
- Type erasure/monomorphization for generics
- Type inference engine

**Current Status:**
- ✅ Type registration works
- ✅ Type metadata can be queried
- ❌ Runtime type checking NOT implemented
- ❌ Generic instantiation NOT implemented
- ❌ Type inference NOT implemented

---

## Future Implementation

See `COMPREHENSIVE_IMPLEMENTATION_PLAN_2026-02-14.md` Section 1 for the complete implementation plan:

**Planned Components:**
1. Runtime type checking (~800 lines, 60 tests)
2. Type erasure/monomorphization (~600 lines, 50 tests)
3. Type inference engine (~1200 lines, 100 tests)

**Estimated Effort:** 11 days of development

---

## Usage Patterns (When Fully Implemented)

These patterns will work once runtime checking is implemented:

```simple
# Generic function with type parameter
fn identity<T>(x: T) -> T:
    x

# Union type for error handling
type Result<T, E> = Success(T) | Error(E)

# Intersection type for multiple traits
type Serializable = Readable & Writable

# Refinement type for constrained values
type PositiveInt = i64 where x > 0
type NonEmptyString = text where x.len() > 0
```

**Note:** These examples show the PLANNED syntax. Parser support and runtime checking are not yet complete.

---

## See Also

- `src/core/types.spl` - Implementation source
- `test/unit/core/generic_syntax_spec.spl` - Parser tests (not yet passing)
- `COMPREHENSIVE_IMPLEMENTATION_PLAN_2026-02-14.md` - Full implementation plan
- `DOCUMENTATION_REALITY_CHECK_2026-02-14.md` - Implementation status

---

**Last Updated:** 2026-02-14
**Implementation Status:** Type registry only (5% complete)
**Production Ready:** ❌ No - Registry only, no runtime checking
