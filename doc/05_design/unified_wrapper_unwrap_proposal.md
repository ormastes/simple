# Unified Wrapper Types & `?` Operator Proposal

**Feature**: Universal unwrapping with context-aware `?` operator
**Date**: 2026-01-12
**Status**: Design Proposal
**Syntax**: Uses `<>` for all template/wrapper types

---

## Executive Summary

Unify all wrapper types (Option, Result, Gpu, Promise, user-defined) under a single `ContextWrapper` trait, enabling:

- ✅ **Bidirectional `?` operator**: Host ↔ Gpu, unwrap errors, options
- ✅ **User-definable wrappers**: via `__init__.spl` configuration
- ✅ **Context-aware transfers**: `?` knows current execution context
- ✅ **Host is default**: No annotation needed for CPU code
- ✅ **`@async` eliminated**: Async is implicit, `@sync` marks synchronous code
- ✅ **Consistent `<>` syntax**: All templates/wrappers use angle brackets

---

## 1. Core Concepts

### 1.1 Wrapper Types vs Template Types

**Both use `<>` syntax**:
- **Template types**: Generic data structures (`List<T>`, `Dict<K,V>`)
- **Wrapper types**: Context/computation wrappers (`Option<T>`, `Gpu<T>`, `Result<T,E>`)

### 1.2 Execution Contexts

```
┌─────────────────────────────────────────┐
│           Host (Default)                │
│  All code runs here unless specified    │
│                                          │
│  ┌────────────────────────────────────┐ │
│  │  @gpu        → Gpu<T>              │ │
│  │  @distributed → Remote<T>          │ │
│  │  @fpga       → Fpga<T>             │ │
│  │  @custom     → UserWrapper<T>      │ │
│  └────────────────────────────────────┘ │
│                                          │
│  Orthogonal wrappers:                   │
│  - Option<T>   (nullable)               │
│  - Result<T,E> (fallible)               │
└─────────────────────────────────────────┘
```

---

## 2. Syntax Examples

### 2.1 Context Annotations

```simple
# Host context (DEFAULT - no annotation)
fn process(x: i32) -> i32:
    x * 2

# GPU context
@gpu
fn matmul(a: Tensor, b: Tensor) -> Tensor:
    a @ b

# GPU with specific device
@gpu(device: 0)
fn train(model: Model) -> Model:
    model.forward().backward()

# User-defined context
@distributed
fn map_reduce(data: List<i32>) -> i32:
    data.parallel_map(|x| x * 2).reduce(|a,b| a + b)
```

### 2.2 Wrapper Types

```simple
# Context wrappers
Gpu<T>              # GPU computation result
Gpu<T, device>      # Specific device
Remote<T>           # Distributed computation
Fpga<T>             # FPGA acceleration

# Error/nullable wrappers (orthogonal)
Option<T>           # May be None
Result<T, E>        # May be Err(e)

# Composed
Gpu<Option<Tensor>>     # GPU holds optional tensor
Result<Gpu<T>, Error>   # GPU operation may fail
```

---

## 3. The Unified `?` Operator

### 3.1 Core Trait

```simple
trait ContextWrapper<T>:
    """Types that can be unwrapped with ?"""

    type Inner = T
    type PropagateOn = Self  # What to return on failure

    # Unwrap in target context
    fn try_unwrap(target_ctx: ExecutionContext) -> T | PropagateOn

    # Check if ready (for async wrappers)
    fn is_ready() -> bool = true

enum ExecutionContext:
    Host
    Gpu(device: u32)
    Custom(name: String)
```

### 3.2 Bidirectional Context Transfer

The `?` operator transfers **to current execution context**:

```simple
# In HOST context:
fn on_host():
    val gpu_result: Gpu<Tensor> = compute_on_gpu()
    val tensor: Tensor = gpu_result?    # Gpu → Host (download)

# In GPU context:
@gpu
fn on_gpu(host_data: Tensor) -> Tensor:
    val local: Tensor = host_data?      # Host → Gpu (upload)
    local * 2
```

### 3.3 Rules Table

| Source Type | Current Context | `?` Result | Transfer Action |
|-------------|-----------------|------------|-----------------|
| `Gpu<T>` | Host | `T` | GPU→Host download |
| `T` (host value) | @gpu function | `T` | Host→GPU upload |
| `Option<T>` | any | `T` or return None | Unwrap optional |
| `Result<T,E>` | any | `T` or return Err(e) | Propagate error |
| `Gpu<Option<T>>` | Host | `T` | Download + unwrap |
| `Remote<T>` | Host | `T` | Network fetch |
| `Fpga<T>` | Host | `T` | FPGA→Host readback |

### 3.4 Implementation Examples

```simple
# Option wrapper
impl<T> ContextWrapper<T> for Option<T>:
    fn try_unwrap(target_ctx: ExecutionContext) -> T | Option<T>:
        match self:
            case Some(v): return v
            case None: return None  # Propagates as early return

# Result wrapper
impl<T, E> ContextWrapper<T> for Result<T, E>:
    fn try_unwrap(target_ctx: ExecutionContext) -> T | Result<T, E>:
        match self:
            case Ok(v): return v
            case Err(e): return Err(e)  # Propagates error

# Gpu wrapper (bidirectional)
impl<T> ContextWrapper<T> for Gpu<T>:
    fn try_unwrap(target_ctx: ExecutionContext) -> T | Gpu<T>:
        match target_ctx:
            case ExecutionContext.Host:
                self.download()  # Gpu → Host
            case ExecutionContext.Gpu(d):
                if d == self.device:
                    self.get_ref()  # Same device, no transfer
                else:
                    self.transfer_to(d)  # P2P GPU transfer
```

---

## 4. Chaining and Composition

### 4.1 Multiple `?` Operators

```simple
@gpu
fn pipeline(input: Option<Tensor>) -> Result<Tensor, Error>:
    # First ?: Option<Tensor> → Tensor (unwrap)
    # Implicit: Tensor (host) → Tensor (gpu upload)
    val data = input?

    # Compute on GPU
    val result = expensive_compute(data)

    Ok(result)

# Call from host
fn main():
    val gpu_result: Gpu<Result<Tensor, Error>> = pipeline(Some(tensor))

    # First ?: Gpu → Host download
    val host_result: Result<Tensor, Error> = gpu_result?

    # Second ?: Result → Tensor (unwrap or propagate error)
    val final: Tensor = host_result?

    # Or chain both: ??
    val final: Tensor = gpu_result??
```

### 4.2 Nested Wrappers

```simple
# Order matters
type A = Gpu<Option<T>>     # GPU holds optional value
type B = Option<Gpu<T>>     # Optional GPU computation

# Unwrapping A
val a: Gpu<Option<T>> = compute()
val inner: Option<T> = a?      # Download from GPU
val value: T = inner?          # Unwrap option
# Or: val value: T = a??

# Unwrapping B
val b: Option<Gpu<T>> = maybe_compute()
val gpu: Gpu<T> = b?           # Unwrap option
val value: T = gpu?            # Download from GPU
# Or: val value: T = b??
```

---

## 5. User-Definable Wrappers

### 5.1 Define in `__init__.spl`

```simple
# my_project/__init__.spl

#[define_context(
    name: "distributed",
    wrapper: Remote,
    annotation: "@distributed",
)]

#[impl_wrapper(Remote)]
impl<T> ContextWrapper<T> for Remote<T>:
    fn try_unwrap(target_ctx: ExecutionContext) -> T | Remote<T>:
        match target_ctx:
            case ExecutionContext.Host:
                self.fetch_from_cluster()
            case ExecutionContext.Custom("distributed"):
                self  # Already distributed
            case _:
                panic("Cannot transfer to this context")
```

### 5.2 Using Custom Wrappers

```simple
# After defining in __init__.spl

@distributed
fn map_reduce(data: List<i32>) -> i32:
    data.map(|x| x * 2).reduce(|a, b| a + b)

# Usage
fn main():
    val result: Remote<i32> = map_reduce(data)
    val local: i32 = result?    # Remote → Host fetch

    print("Result: {}", local)
```

### 5.3 FPGA Example

```simple
# fpga_project/__init__.spl

#[define_context(
    name: "fpga",
    wrapper: Fpga,
    annotation: "@fpga",
)]

impl<T> ContextWrapper<T> for Fpga<T>:
    fn try_unwrap(target_ctx: ExecutionContext) -> T | Fpga<T>:
        match target_ctx:
            case ExecutionContext.Host:
                self.readback()  # FPGA → Host
            case ExecutionContext.Custom("fpga"):
                self
            case _:
                panic("Cannot transfer to {}", target_ctx)

# Usage
@fpga
fn hardware_fft(signal: Signal) -> Signal:
    fft(signal)

fn main():
    val fpga_result: Fpga<Signal> = hardware_fft(input)
    val output: Signal = fpga_result?  # FPGA → Host readback
```

---

## 6. Module-Level Defaults

### 6.1 Context Defaults

```simple
# simple/std_lib/src/ml/__init__.spl

#[context(default: gpu)]        # All functions default to @gpu
#[wrapper(Gpu)]                 # Return types auto-wrapped

export use tensor.*
export use model.*

# Now all functions in this module are @gpu by default
fn train(model: Model) -> Model:  # Returns Gpu<Model>
    model.forward().backward()
```

### 6.2 Override Defaults

```simple
# In ml/__init__.spl, context defaults to @gpu

# This function runs on GPU (default)
fn forward(x: Tensor) -> Tensor:
    x.relu()

# Explicit host override
@host
fn load_data(path: String) -> Tensor:
    File.read(path).parse()
```

---

## 7. `@async` Elimination

### 7.1 Async is Default

```simple
# OLD (deprecated):
@async
fn fetch_user(id: i32) -> User:
    await http.get("/users/{}", id)

# NEW: async is implicit
fn fetch_user(id: i32) -> User:
    http.get("/users/{}", id)  # Suspends implicitly

# Explicit sync
@sync
fn compute(x: i32) -> i32:
    x * 2  # Guaranteed not to suspend
```

### 7.2 Effect Inference

```simple
# Compiler infers effects automatically
fn process() -> Result<Data, Error>:
    val response = http.get(url)?  # Inferred: async + fallible
    val data = parse(response)?     # Inferred: fallible
    Ok(data)

# Equivalent to:
# @async @fallible
# fn process() -> Result<Data, Error>
```

---

## 8. Complete Example: ML Pipeline

```simple
# simple/std_lib/src/ml/__init__.spl
#[context(default: gpu)]
#[wrapper(Gpu)]

# ml/model.spl
struct Model:
    weights: Tensor

# Runs on GPU by default (from __init__.spl)
fn train(model: Model, data: Tensor) -> Model:
    val loss = model.forward(data)
    val grads = loss.backward()
    model.update(grads)

# main.spl
fn main() -> Result<(), Error>:
    # Load data on host
    val host_data = File.read("train.csv")?
    val parsed = parse_csv(host_data)?

    # Create model
    val model = Model.new()

    # Train returns Gpu<Model> (from ml module)
    val gpu_model: Gpu<Model> = train(model, parsed)

    # Download result
    val final_model: Model = gpu_model?

    # Save
    File.write("model.bin", final_model.serialize())
    Ok(())
```

---

## 9. Comparison with Other Languages

| Feature | Simple (This Proposal) | Rust | Swift | Kotlin |
|---------|------------------------|------|-------|--------|
| **Unwrap operator** | `?` (universal) | `?` (Result), `.await` | `try?`, `await` | `?:`, suspend |
| **Generic syntax** | `<>` | `<>` | `<>` | `<>` |
| **GPU types** | `Gpu<T>` with `?` | Manual | Manual | Manual |
| **Async** | Implicit | Explicit `.await` | Explicit `await` | `suspend` |
| **User wrappers** | ✅ `__init__.spl` | ❌ No | ❌ No | ❌ No |
| **Bidirectional `?`** | ✅ Context-aware | ❌ One direction | ❌ One direction | ❌ One direction |

---

## 10. Implementation Roadmap

### Phase 1: Parser & Syntax (2 weeks)
- [ ] Add `<>` support for generics
- [ ] Deprecate `[]` with warnings
- [ ] Parse `@gpu`, `@host`, `@distributed` annotations
- [ ] Parse `#[define_context]` in `__init__.spl`

### Phase 2: Type System (3 weeks)
- [ ] Define `ContextWrapper` trait
- [ ] Implement for `Option`, `Result`, `Gpu`
- [ ] Add `ExecutionContext` enum
- [ ] Extend `?` operator typechecking

### Phase 3: Effect System (2 weeks)
- [ ] Make async default, add `@sync`
- [ ] Remove `@async` annotation
- [ ] Update effect inference

### Phase 4: Codegen (3 weeks)
- [ ] Generate transfer calls for `?`
- [ ] Bidirectional GPU↔Host transfers
- [ ] Optimize transfer elimination

### Phase 5: Stdlib Migration (1 week)
- [ ] Update all `[]` → `<>` in stdlib
- [ ] Add `ContextWrapper` impls
- [ ] Update documentation

### Phase 6: Testing (2 weeks)
- [ ] Unit tests for `?` operator
- [ ] Integration tests for contexts
- [ ] Performance benchmarks

**Total**: ~13 weeks

---

## 11. Migration Guide

### 11.1 Syntax Migration

```bash
# Auto-migrate [] to <>
simple migrate --fix-generics src/
```

### 11.2 Manual Changes

```simple
# Before
List[Int]
Option[User]
Result[T, E]
fn map[T, U](f: fn(T) -> U) -> List[U]

# After
List<Int>
Option<User>
Result<T, E>
fn map<T, U>(f: fn(T) -> U) -> List<U>
```

### 11.3 `@async` Removal

```simple
# Before
@async
fn fetch() -> Data:
    await http.get(url)

# After (async is implicit)
fn fetch() -> Data:
    http.get(url)
```

---

## 12. Open Questions

1. **Ambiguity with comparison operators**:
   - How to parse `Foo<Bar>` vs `Foo < Bar`?
   - **Answer**: Use lookahead - if followed by `,` or `>`, it's generic

2. **Shift operator `>>` vs nested generics**:
   - `Vec<Vec<i32>>` vs `x >> y`
   - **Answer**: Require space for shift: `x >> y`, no space for generics

3. **Type inference for `?`**:
   - When does `?` need explicit type annotation?
   - **Answer**: Almost never - context provides target type

4. **Custom context conflicts**:
   - What if two modules define same context name?
   - **Answer**: Namespaced: `module::@context_name`

---

## 13. Conclusion

**Recommendation**: Implement this unified approach for:

✅ **Consistency**: All wrappers use `<>` and work with `?`
✅ **Extensibility**: Users can define custom contexts
✅ **Simplicity**: Single operator for all unwrapping
✅ **Power**: Bidirectional transfers, context-aware
✅ **Familiarity**: `<>` matches industry standard

**Next Steps**:
1. Gather community feedback
2. Prototype parser with `<>` support
3. Implement `ContextWrapper` trait
4. Migrate stdlib to new syntax

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-12
**Status**: Design Proposal - Ready for Review
