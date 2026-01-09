# Language

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| 11 | Classes | Object-oriented programming with class definitions, typed fields, methods, static methods, and struct-literal instantiation. Supports single inheritance. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/data_structures.md](../../../docs/spec/data_structures.md#feature-11) |
| 12 | Functions | First-class functions with lexical closure. Supports named functions, anonymous lambdas, default parameters, variadic arguments, and higher-order functions like map/filter/reduce. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/functions.md](../../../docs/spec/functions.md#feature-12) |
| 14 | Structs | Struct type for grouping related data. Supports typed fields, struct literals, and field access. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/data_structures.md](../../../docs/spec/data_structures.md#feature-14) |
| 15 | Variables | Variable declarations with let for immutable bindings and let mut for mutable bindings. Supports type annotations and inference. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/syntax.md](../../../docs/spec/syntax.md#feature-15) |
| 17 | Methods | Instance methods with self parameter, static methods, and method chaining. Methods are defined inside class bodies. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/data_structures.md](../../../docs/spec/data_structures.md#feature-17) |
| 24 | Closures | Lambda functions (anonymous functions) with lexical closure. Captures variables from enclosing scope. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/functions.md](../../../docs/spec/functions.md#feature-24) |
| 28 | Imports | Module system with import statements. Supports importing modules, specific items, and aliased imports. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| 29 | Macros | Compile-time code generation with builtin and user-defined macros. Includes vec!, assert!, assert_eq!, format!, panic!, dbg! and custom macro definitions. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/metaprogramming.md](../../../docs/spec/metaprogramming.md#feature-29) |
| 31 | Traits | Trait definitions for shared behavior. Supports impl Trait for Type, default methods, dynamic dispatch with dyn Trait, and TraitObject coercion. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/traits.md](../../../docs/spec/traits.md#feature-31) |
