# Classes (Object-Oriented Programming)

*Source: `simple/std_lib/test/features/language/classes_spec.spl`*

---

# Classes (Object-Oriented Programming)

**Feature ID:** #11
**Category:** Language
**Difficulty:** 4/5 (Advanced)
**Status:** Complete

## Overview

Classes in Simple provide nominal typing and object-oriented programming with struct-literal syntax
for instantiation. Unlike Python's dynamic classes, Simple classes have typed fields and support
methods (including implicit `self`), static methods, and single inheritance.

**Key Features:**
- Typed field declarations
- Struct-literal instantiation: `Point { x: 3, y: 4 }`
- Instance methods with implicit `self` parameter
- Static methods (class methods without `self`)
- Field access via dot notation
- Single inheritance (planned)

## Syntax

### Class Definition

```simple
class ClassName:
    field1: Type1
    field2: Type2

    fn method_name():
        # self is implicit
        return self.field1

    static fn static_method(param):
        # No self - static method
        return ClassName { field1: value1, field2: value2 }
```

**Grammar:**
```
class_def = 'class' identifier (':' identifier)? ':' NEWLINE INDENT (field_def | method_def)+ DEDENT
field_def = identifier ':' type NEWLINE
method_def = ('static')? 'fn' identifier '(' params? ')' ('->' type)? ':' body
```

### Instantiation

```simple
val instance = ClassName { field1: value1, field2: value2 }
```

### Method Calls

```simple
instance.method()       # Instance method (self is implicit)
ClassName.static_method(args)  # Static method
```

## Runtime Representation

**Class Values:**
```rust
pub struct ClassInstance {
    class_name: String,
    fields: HashMap<String, RuntimeValue>,
}
```

**Method Dispatch:**
- Instance methods: Bind `self` to receiver object automatically
- Static methods: No `self` binding, called on class name
- Field access: Direct HashMap lookup

## Comparison with Other Languages

| Feature | Simple | Python | Java | Rust | Scala |
|---------|--------|--------|------|------|-------|
| Instantiation | `Point { x, y }` | `Point(x, y)` | `new Point(x, y)` | `Point { x, y }` | `new Point(x, y)` |
| Fields | Typed | Dynamic | Typed | Typed | Typed |
| Methods | Implicit self | Explicit self | Implicit this | Explicit self | Implicit this |
| Static methods | ✅ Yes | ✅ @staticmethod | ✅ Yes | ✅ Yes | ✅ Yes |
| Inheritance | ⚠️ Planned | ✅ Multiple | ✅ Single | ❌ No (traits) | ✅ Multiple |
| Visibility | ⚠️ All public | ⚠️ Convention-based | ✅ public/private | ✅ pub/private | ✅ public/private |

## Common Patterns

### Constructor Pattern
```simple
class Vector:
    x: f32
    y: f32

    static fn new(x: f32, y: f32) -> Vector:
        return Vector { x: x, y: y }

    static fn zero() -> Vector:
        return Vector { x: 0.0, y: 0.0 }
```

### Builder Pattern
```simple
class ConfigBuilder:
    host: text
    port: i32

    static fn new() -> ConfigBuilder:
        return ConfigBuilder { host: "localhost", port: 8080 }

    me with_host(h: text) -> ConfigBuilder:
        self.host = h
        return self
```

## Implementation Files

**Parser:** `src/parser/src/statements/mod.rs` - Class definition parsing
**Interpreter:** `src/compiler/src/interpreter_method.rs` - Method calls and self binding
**Runtime:** `src/runtime/src/value/objects.rs` - Class instance representation
**Tests:** `src/driver/tests/interpreter_oop_tests.rs` - OOP tests

## Related Features

- **Structs (#TBD):** Classes are nominal types (named types)
- **Methods (#TBD):** Implicit self for instance methods
- **Type System (#1):** Typed fields
- **Functions (#12):** Static methods are functions

## Limitations and Future Work

**Current Limitations:**
- No inheritance (planned)
- No access modifiers (all public)
- No constructors (use static methods)
- No destructors
- No operator overloading

**Planned Features:**
- Single inheritance with `class Child: Parent`
- Access modifiers: `private`, `public`
- Traits/interfaces
- Properties with getters/setters
- Operator overloading

## Class Definitions and Basic Features

    Classes provide nominal typing with struct-literal syntax. Fields are typed, and instances
    are created using struct-literal syntax `ClassName { field: value }`.

    **Instance Methods:** Use implicit `self` to access fields
    **Static Methods:** No `self`, called on class name
    **Field Access:** Dot notation `instance.field`

**Given** a class definition with typed fields
        **When** instantiating the class with struct-literal syntax
        **Then** an instance is created with the specified field values

        **Pattern:** Data class for grouping related values with types.
        **Implementation:** `src/runtime/src/value/objects.rs:ClassInstance`

**Given** a class with instance methods
        **When** calling methods on an instance
        **Then** methods access instance fields via implicit `self`

        Instance methods automatically bind `self` to the receiver object.
        No explicit `self` parameter in method signature.

        **Pattern:** Encapsulation - methods operate on object state.

**Given** a class with static methods (no `self`)
        **When** calling static methods on the class name
        **Then** static methods create or operate on class instances

        Static methods are class-level functions, typically used for
        constructors (new pattern) or factory methods.

        **Pattern:** Constructor pattern - `static fn new()` replaces constructors.

## Classes with Complex Field Types

    Classes can have fields of any type, including collections (List) and other class instances.
    This enables composition and data structure design.

    **Supported Field Types:**
    - Primitives: i32, f32, bool, text
    - Collections: List, Map (when available)
    - Other classes: Composition pattern
    - Option/Result: For nullable/fallible fields

**Given** a class with a List field
        **When** mutating the list through methods
        **Then** the list can store and track elements

        Classes can encapsulate collections, providing controlled access through methods.

        **Pattern:** Collection wrapper - class provides interface to internal collection.
        **Note:** Lists are currently immutable, so `self.items = self.items + [item]` creates new list.

**Given** a class with a field of another class type
        **When** instantiating with nested struct-literal syntax
        **Then** creates a composition relationship

        Classes can contain instances of other classes, enabling composition and
        complex data structures.

        **Pattern:** Composition - building complex types from simpler types.
        **Field Access:** Chained dot notation `outer.inner.x`
