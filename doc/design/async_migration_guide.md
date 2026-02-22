# Async Migration Guide: GC ↔ NoGC Patterns

How to write async code that works across GC and NoGC memory modes in Simple. References the cross-language async research (`doc/research/async_patterns_cross_language.md`) and the nogc_async_mut architecture (`doc/guide/nogc_async_mut_architecture.md`).

**Updated:** 2026-02-22

---

## Memory Model Differences

| Aspect | GC (per-task heap) | NoGC (arena) |
|--------|-------------------|--------------|
| **Allocation** | `gc<T>` in task heap, GC-traced | Arena bump alloc, freed on task end |
| **Deallocation** | GC traces task heap periodically | Arena freed atomically on task end |
| **Cross-task sharing** | Copy on send (mailbox semantics) | Move on send (ownership transfer) |
| **Self-references** | Free — GC handles reference cycles | Must be explicit (IDs, not pointers) |
| **Handle wrapping** | `owns_handle: bool` conditional drop | No `owns_handle` — unconditional drop |
| **Borrowed views** | `Wrapper(handle: h, owns_handle: false)` | Direct FFI call, no wrapper |
| **Tensor lifetime** | GC manages shared handles | Explicit `tensor_free(handle)` |

### Practical Impact

```simple
# GC mode — shared tensor, GC manages lifetime
class GcTensor:
    handle: i64
    owns_handle: bool

    fn drop():
        if self.owns_handle:
            rt_torch_torchtensor_free(self.handle)

    fn sub(other: GcTensor) -> GcTensor:
        val result_handle = rt_torch_torchtensor_sub(self.handle, other.handle)
        # Mark intermediate as borrowed to prevent double-free
        var temp = GcTensor(handle: other.handle, owns_handle: false)
        GcTensor(handle: result_handle, owns_handle: true)

# NoGC mode — explicit ownership, no conditional drop
class NogcTensor:
    handle: i64

    fn drop():
        rt_torch_torchtensor_free(self.handle)

    fn sub(other_handle: i64) -> NogcTensor:
        val result_handle = rt_torch_torchtensor_sub(self.handle, other_handle)
        NogcTensor(handle: result_handle)
```

---

## Ownership of Async State Machines

### GC Mode

Closures capture `gc<T>` references freely. No pinning needed because the GC can relocate objects and update references:

```simple
# GC: closure captures gc<Tensor> — GC keeps it alive
fn async_train(model: GcTensor):
    val runtime = HostRuntime.new()
    runtime.run_task(\:
        # model is gc<GcTensor>, captured by reference
        val loss = model.forward(input)
        loss.backward()
    )
```

### NoGC Mode

Closures capture by value. For self-referential state, use explicit state structs:

```simple
# NoGC: closure captures tensor handle (i64), not the wrapper
fn async_train(model_handle: i64):
    val runtime = HostRuntime.new()
    runtime.run_task(\:
        # model_handle is i64, captured by value (copy)
        val loss_handle = rt_forward(model_handle, input_handle)
        rt_backward(loss_handle)
        rt_torch_torchtensor_free(loss_handle)
    )
```

### Migration Pattern

1. Replace `gc<T>` captures with handle (i64) captures
2. Add explicit `free()` calls at end of task
3. Use return values for output instead of mutable shared state

---

## Channel / Mailbox Buffer Management

### GC Mode

- Unbounded growable mailbox
- GC collects unreferenced messages automatically
- No backpressure — producer can outpace consumer indefinitely

```simple
# GC: unbounded, GC handles cleanup
val mailbox = Mailbox.new()
mailbox.send(large_tensor)  # Always succeeds
# GC reclaims large_tensor when no longer referenced
```

### NoGC Mode

- Bounded capacity via `MailboxConfig`
- Backpressure via `SendResult` (success/full/closed)
- Messages freed when consumed or mailbox destroyed

```simple
# NoGC: bounded, explicit backpressure
val config = MailboxConfig__default()  # capacity limited
val mailbox = Mailbox__new(config)
val result = mailbox.send(data)
if result != SEND_SUCCESS:
    # Handle backpressure — retry, drop, or buffer
    handle_full_mailbox()
```

### Migration Pattern

1. Add bounded capacity to all mailboxes
2. Handle `SendResult` — don't assume sends always succeed
3. Size mailbox capacity based on expected message throughput

---

## Closure Captures Across Await Points

### Known Limitation

Nested closures can READ outer variables but CANNOT MODIFY them (changes don't persist). This affects both GC and NoGC modes.

### Safe Patterns

```simple
# UNSAFE: mutation in nested closure (won't persist)
var count = 0
runtime.run_task(\:
    count = count + 1  # count stays 0 in outer scope
)

# SAFE: return values
fn run_task() -> i64:
    var count = 0
    count = count + 1
    count

# SAFE: class state
class Counter:
    value: i64
    me increment():
        self.value = self.value + 1

# SAFE: module-level functions (module closures work correctly)
var module_count = 0
fn increment_count():
    module_count = module_count + 1
```

---

## Actor State Isolation

### GC Mode

- `gc<ActorState>` — arbitrary object graphs with back-references
- GC handles cycles in actor state
- Actor death triggers GC of entire actor heap (per-process GC)

```simple
# GC: complex state graph with cycles OK
class GcActorState:
    parent: GcActorRef?       # Back-reference — GC handles cycle
    children: [GcActorRef]
    data: gc<HashMap>
```

### NoGC Mode

- `ActorHeap` arena — flat state, IDs instead of direct references
- No cycles possible (no references, only IDs)
- Actor death frees entire arena instantly

```simple
# NoGC: flat state with IDs
class NogcActorState:
    parent_id: ActorId?       # ID, not reference
    child_ids: [ActorId]
    data: HashMap             # Owned, freed with arena

# HeapConfig presets:
# HeapConfig__default()      — 2KB–16MB, GC enabled
# HeapConfig__small()        — 512B–4KB, GC enabled
# HeapConfig__large()        — 64KB–64MB, GC enabled
# HeapConfig__no_gc(size)    — fixed arena, no GC
```

### Migration Pattern

1. Replace direct references with `ActorId` lookups
2. Choose `HeapConfig` preset based on actor workload
3. For short-lived actors: `HeapConfig__no_gc(size)` — arena freed on death
4. For long-lived actors: `HeapConfig__default()` — per-actor GC

---

## Cancellation and Cleanup

### GC Mode

- Eventual finalization — GC will eventually collect abandoned resources
- No deterministic timing for cleanup
- Cancelled tasks' resources freed "eventually" by GC

### NoGC Mode

- `CancellationToken` for cooperative cancellation
- Arena freed immediately on task end
- Structured concurrency via `Supervisor` + `Monitor`

```simple
# NoGC: structured cancellation
val token = CancellationToken.new()

supervisor.spawn_child(\:
    # Check cancellation periodically
    if token.is_cancelled():
        return  # Early exit, arena freed
    do_work()
)

# Cancel all children
token.cancel()
```

### Migration Pattern

1. Add `CancellationToken` to all long-running tasks
2. Check `token.is_cancelled()` in loops and between phases
3. Use `Supervisor` for task group lifecycle
4. Replace GC finalization with explicit cleanup in cancel handlers

---

## Future / Promise Lifecycle

| Aspect | Embedded Runtime | Host Runtime | GC Future |
|--------|-----------------|--------------|-----------|
| **Storage** | Inline value, fixed slot | Heap-allocated | `gc<Future<T>>`, ref-counted |
| **Capacity** | MAX_FUTURES=32 | Unbounded | Unbounded (GC managed) |
| **Waker** | Index-based wakeup | Callback Waker struct | GC waker ref |
| **Consumer** | Single consumer | Waker-based multi | Multi-consumer (refcount) |
| **Lifetime** | Slot reused on complete | Freed on drop | GC collects when unreachable |

### Embedded (bare-metal/WASM)

```simple
# Fixed capacity, inline storage
val runtime = EmbeddedRuntime.new()  # MAX_FUTURES=32
val handle = runtime.spawn(\: compute())
val result = runtime.block_on(handle)
# Slot immediately available for reuse
```

### Host (desktop/server)

```simple
# Dynamic capacity, heap storage
val runtime = HostRuntime.new()
val handle = runtime.run_task(\: compute())
val result = runtime.block_on(handle.join())
# Future freed when handle dropped
```

---

## Cross-Language Patterns Applied to Simple

### Erlang per-process GC → `actor_heap.spl`

Simple's `ActorHeap` directly implements Erlang's per-process heap:
- Each actor has isolated heap with configurable size
- Generational GC (young/old) for long-lived actors
- Arena mode (`no_gc` preset) for short-lived actors
- Actor death frees entire heap — no leak risk

### Zig Io interface → `async_unified.spl`

Simple avoids function coloring via `async_unified.spl`:
- Same API for both embedded and host runtimes
- No `async`/`await` keyword requirement
- Runtime selection at configuration time, not in function signatures
- Future: `@config(runtime: "host" | "embedded")` for compile-time selection

### Swift Sendable → `effects.spl`

Simple's `@async` annotation maps to Swift's `Sendable`:
- Marks functions that may suspend
- Future: compile-time checking that `@async` functions don't capture non-sendable state
- Effect annotations (`@io`, `@pure`, `@sync`) provide additional guarantees

### Kotlin structured concurrency → `Supervisor` + `CancellationToken`

Simple's OTP-style supervision provides Kotlin-equivalent structured concurrency:
- `Supervisor` = `coroutineScope` (parent-child lifecycle binding)
- `CancellationToken` = Kotlin `Job.cancel()` (cooperative cancellation)
- `Monitor` = structured exception propagation
- `JoinSet` / `FuturesUnordered` = task group collection

---

## gc_async_mut Clarification

The `gc_async_mut/` directory contains **sync GPU/ML code**, not async code:

| Module | Content | Why gc_async_mut? |
|--------|---------|-------------------|
| `torch/` | Tensor operations, training, DynLoader | GC manages shared tensor handles |
| `cuda/` | CUDA stream/event/memory wrappers | `owns_handle` conditional drop |
| `gpu/` | High-level GPU memory management | Explicit lifecycle (no owns_handle) |
| `gpu_runtime/` | GPU runtime utilities | Borrowed-view pattern for temp access |
| `pure/` | Math/ML algorithms (tensors, NN, autograd) | Pure value types (no FFI handles) |

**Key insight:** CUDA streams provide hardware-level async, but Simple's wrappers are all synchronous function calls. The "async" in `gc_async_mut` refers to the module zone's capability (GC + async-capable), not the actual code behavior.

**What would true async GPU look like?**
```simple
# Future pattern (not yet implemented)
fn async_train(model: Tensor, data: DataLoader):
    val stream = CudaStream.create(device: 0)
    runtime.run_task(\:
        for batch in data:
            val loss = model.forward_async(batch, stream)
            val grad = loss.backward_async(stream)
            stream.sync()  # Wait for GPU ops
            model.update(grad)
    )
```

---

## Modules with NoGC Copies

All modules below have NoGC variants in `nogc_sync_mut/`. The originals are **retained** in `gc_async_mut/` for GC-mode users.

| Module | GC Source | NoGC Copy | Changes in NoGC |
|--------|-----------|-----------|-----------------|
| `torch/dyn_ffi.spl` | `gc_async_mut/torch/` | `nogc_sync_mut/torch/` | None — 100% stateless |
| `gpu_driver/` | `gc_async_mut/gpu.spl` | `nogc_sync_mut/gpu_driver/` | Local `extern fn` replaces `compiler.loader.cuda_ffi` import |
| `cuda/` | `gc_async_mut/cuda/` | `nogc_sync_mut/cuda/` | Removed `owns_handle`, unconditional drop |
| `gpu/` | `gc_async_mut/gpu/` | `nogc_sync_mut/gpu/` | Shared types from `common/gpu/` |
| `gpu_runtime/` | `gc_async_mut/gpu_runtime/` | `nogc_sync_mut/gpu_runtime/` | Direct FFI replaces borrowed-view |
| `pure/` | `gc_async_mut/pure/` | `nogc_sync_mut/pure/` | Fixed 6 internal cross-references |

---

## Future: Async GC Module Patterns

When GC-aware async modules are created, they should follow:

### Per-Task Heap (recommended for most cases)

```simple
# Each async task gets its own GC heap
val runtime = GcRuntime.new()
runtime.spawn_with_heap(HeapConfig__default(), \:
    # Allocations go to task-local heap
    val tensor = GcTensor.create(...)
    val result = tensor.forward(input)
    # Task-local GC runs independently
)
```

### Shared-Nothing Messaging

```simple
# Tasks communicate via copy-on-send
val ch = channel_new()
runtime.spawn(\:
    val data = compute()
    ch.send(data.clone())  # Deep copy across task boundary
)
val result = ch.recv()     # Received in our task's heap
```

### Arena Fallback for Hot Paths

```simple
# Short-lived tasks use arena (no GC overhead)
runtime.spawn_with_heap(HeapConfig__no_gc(4096), \:
    # Fixed arena — fast alloc, freed entirely on task end
    process_batch(data)
    # No GC pauses, no fragmentation
)
```

---

## Cross-References

- **Cross-language patterns:** [`doc/research/async_patterns_cross_language.md`](../research/async_patterns_cross_language.md)
- **nogc_async_mut architecture:** [`doc/guide/nogc_async_mut_architecture.md`](../guide/nogc_async_mut_architecture.md)
- **Module parity:** [`doc/design/gc_nogc_module_parity.md`](gc_nogc_module_parity.md)
- **Resource lifecycle:** [`doc/design/resource_lifecycle_manager_design.md`](resource_lifecycle_manager_design.md)
