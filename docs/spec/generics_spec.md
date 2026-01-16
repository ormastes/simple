# generics_spec

*Source: `simple/std_lib/test/features/types/generics_spec.spl`*

---

Generics - Feature #32

Overview:
    Generic type parameters for functions, structs, and enums. Supports single
    and multiple type parameters with angle bracket notation (<T>). Enables
    code reuse and type-safe abstractions without runtime overhead.

Syntax:
    fn identity<T>(x: T) -> T           # Generic function
    struct Box<T>:                      # Generic struct
        value: T
    enum Maybe<T>:                      # Generic enum
        Just(T)
        Nothing
    val b: Box<i64> = Box {value: 42}   # Type instantiation

Implementation:
    - Uses <T> for declarations (angle brackets)
    - Supports single and multiple type parameters
    - Generic functions, structs, and enums
    - Nested generics (e.g., List<Option<i64>>)
    - Type inference from usage
    - Monomorphization for performance

Notes:
    - Uses <T> for declarations and [T] for type arguments
    - Advanced features (where clauses, const generics) pending
    - Complete: generic functions, structs, enums, nested generics
    - Planned: const generics, where clauses, associated types
