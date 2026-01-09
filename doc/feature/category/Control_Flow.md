# Control Flow

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-13"></a>13 | Loops | Loop constructs including for-in loops over iterables, while loops with conditions, and break/continue control. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/syntax.md](../../spec/syntax.md#feature-13) |
| <a id="feature-35"></a>35 | Error Handling | Result-based error handling with Ok/Err variants. Supports unwrap, is_ok/is_err checks, unwrap_or, and the ? operator for error propagation. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/types.md](../../spec/types.md#feature-35) |
| <a id="feature-90"></a>90 | Match Expressions | Powerful pattern matching with exhaustiveness checking. Supports literal patterns, variable binding, wildcard (_), guards, and destructuring. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/functions.md](../../spec/functions.md#feature-90) |
| <a id="feature-91"></a>91 | Conditionals | Conditional statements with if, elif, and else branches. Supports boolean expressions and logical operators. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/syntax.md](../../spec/syntax.md#feature-91) |
