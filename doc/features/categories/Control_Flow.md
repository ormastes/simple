# Control Flow

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| 13 | Loops | Loop constructs including for-in loops over iterables, while loops with conditions, and break/continue control. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/syntax.md](../../../docs/spec/syntax.md#feature-13) |
| 35 | Error Handling | Result-based error handling with Ok/Err variants. Supports unwrap, is_ok/is_err checks, unwrap_or, and the ? operator for error propagation. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/types.md](../../../docs/spec/types.md#feature-35) |
| 90 | Match Expressions | Powerful pattern matching with exhaustiveness checking. Supports literal patterns, variable binding, wildcard (_), guards, and destructuring. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/functions.md](../../../docs/spec/functions.md#feature-90) |
| 91 | Conditionals | Conditional statements with if, elif, and else branches. Supports boolean expressions and logical operators. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/syntax.md](../../../docs/spec/syntax.md#feature-91) |
