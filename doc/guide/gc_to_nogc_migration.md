# GC to NoGC Migration Guide

How to migrate code from GC libraries (`gc_async_mut/`) to NoGC libraries (`nogc_sync_mut/`).

This guide uses the torch library as the primary example but applies to **any** library in the `src/lib/` hierarchy.

---

## Memory Model: gc\<T\> vs unique_pointer\<T\>

| | GC Mode (`gc_async_mut/`) | NoGC Mode (`nogc_sync_mut/`) |
|---|---------|-----------|
| **Default pointer** | `gc<T>` — shared, reference-counted | `unique_pointer<T>` — single owner, RAII |
| **Object lifetime** | GC collects when no references remain | Destroyed when owner scope ends |
| **Sharing** | Implicit — multiple refs to same object | Explicit — must call `clone()` |
| **Pass to function** | Shared reference (no ownership transfer) | Move semantics (ownership transfers) |
| **Return from function** | Shared reference returned | Ownership transferred to caller |
| **Field access** | Through GC reference (may indirect) | Direct (zero-cost) |
| **Memory overhead** | Reference count + GC metadata per object | No overhead (just the object) |
| **Deallocation** | Non-deterministic (GC decides when) | Deterministic (scope exit = free) |

### Why migrate?

- **Deterministic cleanup**: NoGC frees resources exactly when scope ends — critical for GPU memory, file handles, network connections
- **No GC pauses**: Training loops run without GC collection stalls
- **Lower memory overhead**: No reference counting metadata per tensor
- **Explicit ownership**: Forces clear thinking about resource lifetime
- **Better for FFI**: C/C++ libraries expect single-owner semantics

### When to keep GC?

- **Shared data structures**: Graphs, trees with multiple parents
- **Async/concurrent**: Multiple coroutines sharing state
- **Prototyping**: When ownership tracking is too much ceremony

---

## Architecture: Common Interface

Both GC and NoGC torch implementations satisfy the same `TorchBackend` trait defined in `common/torch/interface.spl`.

```
common/torch/
    interface.spl     — TorchBackend trait (handle-level operations)
    __init__.spl      — module marker

nogc_sync_mut/torch/
    backend.spl       — impl TorchBackend for NogcTorchOps
    ffi.spl           — extern fn declarations
    mod.spl           — Tensor class (unique ownership)
    ops.spl           — higher-level ops (handle-level)
    optim.spl         — SGDOptimizer, AdamOptimizer
    torch_training.spl — loss, optimizers, stream, sequential

gc_async_mut/torch/
    backend.spl       — impl TorchBackend for GcTorchOps
    ffi.spl           — extern fn declarations
    dyn_ffi.spl       — DynLoader runtime binding
    mod.spl           — Tensor class (shared ownership)
    ops.spl           — higher-level ops (handle-level)
    optim.spl         — SGDOptimizer, AdamOptimizer
    torch_training.spl — loss, optimizers, stream, sequential
```

### Using the trait for backend-agnostic code

```simple
use std.common.torch.interface.{TorchBackend}

# Write generic code against the trait
fn compute_loss(backend: TorchBackend, logits_h: i64, targets_h: i64) -> i64:
    val log_probs = backend.tensor_log_softmax(logits_h, 1)
    val neg = backend.tensor_neg(log_probs)
    backend.tensor_free(log_probs)
    val gathered = backend.tensor_gather(neg, 1, targets_h)
    backend.tensor_free(neg)
    gathered
```

### Static dispatch (zero overhead)

```simple
use std.common.torch.interface.{TorchBackend}
use std.nogc_sync_mut.torch.backend.{NogcTorchOps}

bind TorchBackend = NogcTorchOps   # compile-time resolution
# All TorchBackend calls become direct FFI calls — no vtable
```

---

## Step-by-Step Migration

### Step 1: Change Imports

```simple
# Before (GC)
use std.gc_async_mut.torch.mod.{Tensor, Linear, Conv2d}
use std.gc_async_mut.torch.torch_training.{MSELoss, SGD, Adam, Sequential}
use std.gc_async_mut.torch.ops.{cross_entropy_loss_tensor, compute_accuracy}
use std.gc_async_mut.torch.optim.{SGDOptimizer, AdamOptimizer}

# After (NoGC)
use std.nogc_sync_mut.torch.mod.{Tensor, Linear, Conv2d}
use std.nogc_sync_mut.torch.torch_training.{MSELoss, SGD, Adam, Sequential}
use std.nogc_sync_mut.torch.ops.{cross_entropy_loss_tensor, compute_accuracy}
use std.nogc_sync_mut.torch.optim.{SGDOptimizer, AdamOptimizer}
```

All class names, function names, and method signatures are identical.

### Step 2: Remove `owns_handle` field

GC Tensor has `handle: i64` and `owns_handle: bool`. NoGC Tensor has only `handle: i64`.

```simple
# GC — needed to track shared vs owned
Tensor(handle: h, owns_handle: true)   # owns the handle
Tensor(handle: h, owns_handle: false)  # borrowed ref

# NoGC — always owns
Tensor(handle: h)                       # unique owner, always owns
```

Search and replace all `Tensor(handle: X, owns_handle: Y)` with `Tensor(handle: X)`.

### Step 3: Remove `owns_handle` manipulation

```simple
# Remove these patterns:
tensor.owns_handle = false     # delete line
tensor.owns_handle = true      # delete line
if self.owns_handle:           # remove condition, keep body
    rt_torch_torchtensor_free(self.handle)
# becomes:
rt_torch_torchtensor_free(self.handle)
```

### Step 4: Add explicit `clone()` for shared usage

In GC mode, passing a tensor to a function shares a reference — the original stays valid. In NoGC mode, ownership moves.

```simple
# GC — t remains valid after process()
val t = Tensor.randn([3, 3])
process(t)
print t.shape()   # OK — t is shared reference

# NoGC — t has moved, use clone() to keep it
val t = Tensor.randn([3, 3])
process(t.clone())
print t.shape()   # OK — t was not moved, clone was moved
```

**Rule**: If you use a tensor after passing it to a function, insert `.clone()` at the call site.

### Step 5: sub()/div() work the same

The GC versions use complex workarounds (create intermediaries, juggle `owns_handle`). NoGC uses direct FFI calls. The API is the same — no code changes needed.

```simple
# Both GC and NoGC
val result = a.sub(b)   # works identically
val result = a.div(b)   # works identically
```

### Step 6: Stream class changes

```simple
# GC Stream — 3 fields
Stream(handle: h, owns_handle: true, device_id: 0)

# NoGC Stream — 2 fields
Stream(handle: h, device_id: 0)
```

---

## Migration Checklist

- [ ] Change all import paths from `gc_async_mut` to `nogc_sync_mut`
- [ ] Remove `owns_handle` from Tensor/Stream construction
- [ ] Remove `owns_handle = true/false` assignments
- [ ] Remove `if self.owns_handle:` guards (keep the body)
- [ ] Add `.clone()` where tensor is used after passing to function
- [ ] Verify sub()/div() calls still work (API unchanged)
- [ ] Update any `-> void` return types to just omit the return type
- [ ] Replace `pass_do_nothing` with `0` (if in closure/it block context)
- [ ] Test: `bin/simple build` to verify files parse
- [ ] Test: `bin/simple test path/to/spec.spl` for specific tests

---

## General Library Migration Pattern

The torch migration pattern applies to **any** library:

### 1. Create module in `nogc_sync_mut/`

Mirror the directory structure from `gc_async_mut/`:

```
gc_async_mut/mylib/
    ffi.spl
    mod.spl
    utils.spl

nogc_sync_mut/mylib/       # create this
    ffi.spl                # duplicate FFI declarations
    mod.spl                # adapt wrapper classes
    utils.spl              # copy if handle-level (no changes needed)
```

### 2. Duplicate FFI declarations

Both modes use the same C/C++ symbols. Duplicate `extern fn` declarations to avoid cross-mode import warnings:

```simple
# nogc_sync_mut/mylib/ffi.spl
extern fn rt_mylib_create() -> i64
extern fn rt_mylib_free(handle: i64)
extern fn rt_mylib_process(handle: i64) -> i64
```

### 3. Adapt wrapper classes

Remove GC-specific ownership tracking:

```simple
# GC version
class Resource:
    handle: i64
    owns_handle: bool

    fn drop():
        if self.owns_handle:
            rt_mylib_free(self.handle)

# NoGC version
class Resource:
    handle: i64

    fn drop():
        rt_mylib_free(self.handle)
```

### 4. Make `drop()` unconditional

GC: conditional on `owns_handle`. NoGC: always frees.

### 5. Simplify workarounds

GC code often has complex patterns to manage shared ownership of intermediaries. NoGC can use direct calls:

```simple
# GC — workaround for shared intermediary
val tmp = create_helper()
val tmp_handle = tmp.handle
tmp.owns_handle = false    # prevent GC from freeing
val result = process(tmp_handle)
rt_free(tmp_handle)        # manual free

# NoGC — direct
val tmp = create_helper()
val result = process(tmp.handle)
tmp.drop()
```

### 6. Define common interface in `common/`

Create convention traits documenting the shared API surface:

```simple
# common/mylib/interface.spl
trait MyLibBackend:
    fn create() -> i64
    fn process(handle: i64) -> i64
    fn free(handle: i64)
```

### 7. Keep function signatures identical

Ensure both GC and NoGC versions have the same method names and parameter types. This enables users to switch by changing only import paths.

---

## Common Pitfalls

### 1. Double-free in NoGC

GC prevents double-free via reference counting. NoGC does not.

```simple
# WRONG — double free in NoGC
val t = Tensor.randn([3])
process(t)       # t ownership moved
t.drop()         # CRASH — t already freed by process()

# CORRECT
val t = Tensor.randn([3])
process(t.clone())  # clone moved, t still valid
t.drop()            # safe
```

### 2. Use-after-move

```simple
# WRONG — t is moved
val t = Tensor.randn([3])
val list = [t]    # t moved into list
print t.shape()   # CRASH — t is gone

# CORRECT
val t = Tensor.randn([3])
val list = [t.clone()]
print t.shape()   # OK
```

### 3. Loop accumulator leaks

In GC mode, intermediate tensors are collected. In NoGC, you must free them:

```simple
# GC — intermediates collected automatically
var total = Tensor.zeros([10])
var i = 0
while i < 100:
    val batch = compute_batch(i)
    total = total.add(batch)   # old total collected by GC
    i = i + 1

# NoGC — must free intermediates
var total = Tensor.zeros([10])
var i = 0
while i < 100:
    val batch = compute_batch(i)
    val new_total = total.add(batch)
    total.drop()           # free old total
    batch.drop()           # free batch
    total = new_total
    i = i + 1
```

### 4. Forgetting to free in error paths

```simple
# WRONG — leak if process() fails
val t = Tensor.randn([3])
val result = process(t.handle)
if result == 0:
    return nil        # t leaks!
t.drop()

# CORRECT — always clean up
val t = Tensor.randn([3])
val result = process(t.handle)
if result == 0:
    t.drop()          # clean up before early return
    return nil
t.drop()
```

---

## Side-by-Side Example: Training Loop

### GC Version

```simple
use std.gc_async_mut.torch.mod.{Tensor, Linear}
use std.gc_async_mut.torch.torch_training.{MSELoss, SGD}

val model = Linear.create(10, 1)
val criterion = MSELoss.create()
val params = model.parameters()
val optimizer = SGD.create(params, 0, 0)

val x = Tensor.randn([32, 10])
val y = Tensor.randn([32, 1])
val pred = model.forward(x)
val loss = criterion.forward(pred, y)
loss.backward()
optimizer.step()
optimizer.zero_grad()
```

### NoGC Version

```simple
use std.nogc_sync_mut.torch.mod.{Tensor, Linear}
use std.nogc_sync_mut.torch.torch_training.{MSELoss, SGD}

val model = Linear.create(10, 1)
val criterion = MSELoss.create()
val params = model.parameters()
val optimizer = SGD.create(params, 0, 0)

val x = Tensor.randn([32, 10])
val y = Tensor.randn([32, 1])
val pred = model.forward(x)
val loss = criterion.forward(pred, y)
loss.backward()
optimizer.step()
optimizer.zero_grad()
```

The code is identical — only the import path differs. Ownership semantics are handled internally by each Tensor class.

---

## Migrated Modules

The following modules have been migrated from `gc_async_mut/` to `nogc_sync_mut/` as of 2026-02-22:

| Module | Source | Destination | Notes |
|--------|--------|-------------|-------|
| `torch` | `gc_async_mut/torch/` | `nogc_sync_mut/torch/` | Reference pattern — complete |
| `cuda` | `gc_async_mut/cuda/` | `nogc_sync_mut/cuda/` | Remove `owns_handle` from 3 classes, unconditional `drop()` |
| `gpu` | `gc_async_mut/gpu/` | `nogc_sync_mut/gpu/` | Redirect torch imports to nogc; types from `common/gpu/` |
| `gpu_runtime` | `gc_async_mut/gpu_runtime/` | `nogc_sync_mut/gpu_runtime/` | Replace borrowed-view pattern with direct FFI calls |
| `pure` | `gc_async_mut/pure/` | `nogc_sync_mut/pure/` | Copy + fix 6 internal `gc_async_mut` cross-references |

### Shared types extracted to `common/`

GPU device types moved to `src/lib/common/gpu/device.spl`:
- `GpuBackend` enum (Cuda, Vulkan, None_)
- `Gpu` struct (backend, device_id, is_initialized)
- `gpu_cuda()`, `gpu_vulkan()`, `gpu_none()` constructors

Both `gc_async_mut/gpu/` and `nogc_sync_mut/gpu/` import from `std.common.gpu.device`.

### `gpu_runtime` borrowed-view redesign

The GC `gpu_runtime/mod.spl` creates temporary wrappers with `owns_handle: false` to call methods on raw handles:

```simple
# GC: borrowed-view pattern (creates temporary wrapper object)
val t = TorchTensorWrapper(handle: h, owns_handle: false)
t.is_cuda()

# NoGC: direct FFI call (no wrapper)
rt_torch_torchtensor_is_cuda(h)
```

---

## Backend-Agnostic Code (Advanced)

For libraries that must support both modes simultaneously:

```simple
use std.common.torch.interface.{TorchBackend}

# Accept any backend via dynamic dispatch
fn train_step(backend: TorchBackend, input_h: i64, target_h: i64, params: [i64], lr: f64) -> [i64]:
    val logits = backend.nn_linear(input_h, params[0], params[1])
    val loss_val = backend.nn_cross_entropy(logits, target_h)

    backend.tensor_backward(logits)
    backend.no_grad_begin()

    var new_params = []
    var i = 0
    while i < params.len():
        val g = backend.tensor_grad(params[i])
        if g != 0:
            val update = backend.tensor_mul_scalar(g, lr)
            val p_new = backend.tensor_sub(params[i], update)
            backend.tensor_free(update)
            backend.tensor_free(params[i])
            new_params = new_params + [p_new]
        else:
            new_params = new_params + [backend.tensor_clone(params[i])]
            backend.tensor_free(params[i])
        i = i + 1

    backend.no_grad_end()
    new_params

# Usage with static dispatch:
# bind TorchBackend = NogcTorchOps
# train_step(NogcTorchOps(), input, target, params, 0.01)
```
