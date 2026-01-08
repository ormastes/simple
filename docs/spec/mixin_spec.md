# Mixin Feature Specification

*Source: `./tests/system/mixin_spec.spl`*

---

# Mixin Feature Specification

## Overview
Mixins provide a way to compose behavior into classes without using inheritance.
They support:
- Field and method composition
- Generic type parameters with inference
- Trait bounds and constraints
- Required methods that targets must implement
- Multiple mixin application

## Syntax
```simple
mixin MixinName<T> where T: Trait {
    field: Type
    
    fn method(self, arg: T) -> Result {
        // implementation
    }
    
    fn required_method(self) -> Type;  // Must be implemented by target
}

class Target with Mixin1, Mixin2<Type> {
    // class body
}
```

### Scenario: Declare a simple mixin with fields

A mixin can declare fields that will be added to any class that uses it.
The mixin syntax follows:
```
mixin Name:
    field_name: Type
```

### Scenario: Mixin with instance methods

Mixins can define methods that operate on `self` and access mixin fields.
These methods become available on any class that applies the mixin.

### Scenario: Generic mixin with type parameter

Mixins support generic type parameters that are unified with concrete types
when applied to a class. The type parameter `T` is inferred from usage.

```
mixin Cache<T>:
    cache: HashMap<str, T>
```

### Scenario: Apply mixin to a class

The `with` keyword applies one or more mixins to a class:
```
class MyClass with Mixin1, Mixin2:
    # class body
```

All mixin fields and methods become available on the class.

### Scenario: Apply multiple mixins to one class

A class can apply multiple mixins by listing them after `with`:
```
class MyClass with Mixin1, Mixin2, Mixin3:
    # body
```

### Scenario: Apply generic mixin with concrete type

When applying a generic mixin, type parameters can be specified explicitly:
```
class MyClass with Cache<User>:
    # T is unified with User
```

### Scenario: Mixin with trait requirements

Mixins can require that the type parameter or target class implements
specific traits using `where` clauses:
```
mixin Serializable<T> where T: Serialize + Deserialize:
    # methods
```

### Scenario: Mixin with required methods

A mixin can declare required methods (without implementation) that must
be provided by the target class:
```
mixin Repository<T>:
    fn table_name(self) -> str;  # Required - no body
    
    fn find_by_id(self, id: i64) -> Option<T>:
        let table = self.table_name()
        # use table in query
```

### Scenario: Access mixin fields from class method

Methods in the target class can access fields provided by mixins:

### Scenario: Call mixin methods from class method

Methods in the target class can call methods provided by mixins:

### Scenario: Type inference for mixin fields and methods

The type system should infer types for:
- Mixin field accesses
- Mixin method return types
- Generic type parameter unification

### Scenario: Mixin can apply another mixin

Mixins themselves can apply other mixins, creating composition:
```
mixin AuditLog with Timestamp:
    # inherits created_at, updated_at from Timestamp
    modified_by: str
```

### Scenario: Detect field name conflicts

If two mixins define the same field name, or a mixin field conflicts
with a class field, the compiler should report an error.

### Scenario: Detect method name conflicts

If two mixins define methods with the same name, the compiler should
report an ambiguity error.
