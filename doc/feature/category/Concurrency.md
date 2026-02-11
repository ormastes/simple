# Concurrency

| ID | Feature | Description | Pure | Hybrid | LLVM | Status | Spec |
|----|---------|-------------|------|--------|------|--------|------|
| <a id="feature-40"></a>40 | Actors | Actor-based concurrency with spawn. Actors run in isolation with message passing. Default concurrency mode for Simple programs. | done | done | done | ✅ done | [spec](../../doc/spec/concurrency.md) |
| <a id="feature-44"></a>44 | Async Default | Functions are async by default in Simple. The `sync` keyword explicitly marks non-suspending functions. | done | done | done | ✅ done | [spec](../../doc/spec/async_default.md) |
| <a id="feature-47"></a>47 | Promise Type | The `Promise[T]` type represents an async computation that will eventually produce a value of type `T`. Async functions implicitly return `Promise[T]`. | done | done | done | ✅ done | [spec](../../doc/spec/async_default.md#promise-type) |
