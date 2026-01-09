# Types

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-10"></a>10 | Basic Types | Primitive types: Int (i64), Float (f64), Bool, String, and Nil. Supports type annotations and inference. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/types.md](../../spec/types.md#feature-10) |
| <a id="feature-16"></a>16 | Enums | Algebraic data types with variants. Supports simple enums, enums with associated data, and pattern matching. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/data_structures.md](../../spec/data_structures.md#feature-16) |
| <a id="feature-18"></a>18 | Memory Types | Reference capability system with GC-managed references (T), unique pointers (&T), shared pointers (*T), weak pointers (-T), and handle pointers (+T). | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/memory.md](../../spec/memory.md#feature-18) |
| <a id="feature-19"></a>19 | Borrowing | Ownership semantics with move, borrow, and lifetime tracking. Ensures memory safety without garbage collection for manual memory types. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/memory.md](../../spec/memory.md#feature-19) |
| <a id="feature-27"></a>27 | Option and Result | Optional values with Some/None and error handling with Ok/Err. Used for nullable values and fallible operations. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/types.md](../../spec/types.md#feature-27) |
| <a id="feature-30"></a>30 | Operators | Full set of operators: arithmetic (+, -, *, /, %), comparison (==, !=, <, >, <=, >=), logical (and, or, not), and bitwise operations. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/syntax.md](../../spec/syntax.md#feature-30) |
| <a id="feature-32"></a>32 | Generics | Generic type parameters for functions, structs, and enums. Supports single and multiple type parameters with bracket notation. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/types.md](../../spec/types.md#feature-32) |
