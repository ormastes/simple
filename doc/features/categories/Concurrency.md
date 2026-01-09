# Concurrency

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| 40 | Actors | Actor-based concurrency with spawn. Actors run in isolation with message passing. Default concurrency mode for Simple programs. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/concurrency.md](../../../docs/spec/concurrency.md#feature-40) |
| 41 | Async/Await | Async functions for non-blocking computation. Includes async fn declarations, effect checking for blocking operations, and await for future resolution. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/concurrency.md](../../../docs/spec/concurrency.md#feature-41) |
| 42 | Generators | Generators for lazy value production using yield. Supports single and multiple yields, state preservation, captured variables, and collection. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/concurrency.md](../../../docs/spec/concurrency.md#feature-42) |
| 43 | Futures | Future values representing async computations. Create with future(), resolve with await. Supports eager evaluation and value capture. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/concurrency.md](../../../docs/spec/concurrency.md#feature-43) |
| 44 | Async Default | Functions are async by default in Simple. The `sync` keyword explicitly marks non-suspending functions. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/async_default.md](../../../docs/spec/async_default.md#feature-44) |
| 45 | Suspension Operator (~) | The `~` operator marks explicit suspension points for async operations, making async control flow visible at the syntax level. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/spec/suspension_operator.md](../../../docs/spec/suspension_operator.md#feature-45) |
| 46 | Effect Inference | The compiler automatically infers whether a function is async or sync based on its body, eliminating the need for explicit annotations in most cases. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| 47 | Promise Type | The `Promise[T]` type represents an async computation that will eventually produce a value of type `T`. Async functions implicitly return `Promise[T]`. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
