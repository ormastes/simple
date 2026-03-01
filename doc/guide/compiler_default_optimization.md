# Compiler Default Optimization — Collection Efficiency

This document covers the 5 collection efficiency anti-patterns detected by the Simple compiler, which patterns the compiler can fix automatically via MIR optimization, and which require manual code changes.

---

## Overview

| Code | Pattern | Severity | Compiler Auto-Fix? | Manual Fix Required? |
|------|---------|----------|--------------------|--------------------|
| COLL001 | `arr = arr + [x]` in loop | CRITICAL | Yes (MIR pass) | Better: fix in source |
| COLL002 | `.contains()` on array in loop | HIGH | No | Yes |
| COLL003 | `.remove(0)` queue drain in loop | HIGH | No | Yes |
| COLL004 | Loop-invariant method call | MEDIUM | Yes (MIR pass) | Better: fix in source |
| COLL005 | Chained `.filter().filter()` | MEDIUM | No | Yes |

**Rule of thumb:** Patterns 1 and 4 can be auto-optimized at the MIR level, but fixing them in source code is always preferred for clarity. Patterns 2, 3, 5 require different data structures or algorithm changes that the compiler cannot safely infer.

---

## Pattern Details

### COLL001 — Array Concat in Loop (CRITICAL)

**The problem:**
```simple
var items = []
for x in 0..n:
    items = items + [x]     # O(n) copy every iteration -> O(n^2) total
```

`arr + [x]` calls `spl_array_concat()` in the runtime, which allocates a **new array** and copies all existing elements plus the new one. In a loop of `n` iterations, this performs `1 + 2 + 3 + ... + n = n(n+1)/2` element copies.

**Why it's bad:** For 10,000 elements, this is ~50 million element copies instead of 10,000.

**Manual fix — use `.push()` (in-place, O(1) amortized):**
```simple
var items = []
for x in 0..n:
    items.push(x)           # In-place mutation, O(1) amortized
```

`.push()` calls `spl_array_push()` which mutates the array in-place. The array starts with capacity 16 and doubles when full (16 -> 32 -> 64 -> ...), so amortized cost per push is O(1).

**Compiler auto-fix (MIR level):** The `collection_opt` pass detects the 3-instruction MIR pattern:
```
Aggregate(tmp, Array(T), [x])     ->  (removed)
Call(result, "+", [arr, tmp])     ->  Call(_, "push", [arr, x])
Copy(arr, result)                 ->  (removed)
```

**Found in compiler codebase (17+ instances):**

| File | Lines | Context |
|------|-------|---------|
| `99.loader/jit_instantiator.spl` | 70-72, 86-88, 109-111, 200-202, 238 | JIT symbol registry, exec mapper |
| `95.interp/mir_interpreter.spl` | 452, 462, 537-539 | Call stack, argument building |
| `50.mir/mir_data.spl` | 414 | Operand list building |
| `70.backend/backend/llvm_native_link.spl` | 92-97 | Object file list assembly |
| `70.backend/backend/native/mod.spl` | 192-204 | SMF byte encoding |
| `core/aop_debug_log.spl` | 100, 101, 128, 136, 147, 164 | Debug log entry accumulation |

---

### COLL002 — `.contains()` on Array in Loop (HIGH)

**The problem:**
```simple
var seen = []
for x in data:
    if seen.contains(x):    # O(n) linear scan each time -> O(n^2) total
        skip
    seen.push(x)
```

Array `.contains()` is O(n) linear scan. Inside a loop, this becomes O(n^2).

**Manual fix — use Dict or Set:**
```simple
var seen = {}                # Dict<text, bool> — O(1) lookup
for x in data:
    if seen.contains_key(x):
        continue
    seen[x] = true
    # ... process x
```

Or with the Set type:
```simple
use std.set.Set

var seen = Set.new()         # O(1) lookup via hash map
for x in data:
    if seen.has(x):
        continue
    seen.insert(x)
```

**Why the compiler cannot auto-fix:** Replacing array with Dict/Set changes the data structure type, which propagates through all code that uses the variable. The compiler cannot safely determine that the array is only used for membership testing.

**Current compiler codebase:** No instances of `.contains()` on arrays inside loops found. Dict `.contains_key()` is correctly used throughout (e.g., `20.hir/inference/infer.spl`, `20.hir/inference/unify.spl`).

---

### COLL003 — `.remove(0)` Queue Drain (HIGH)

**The problem:**
```simple
while queue.len() > 0:
    val item = queue[0]
    queue.remove(0)          # O(n) shift every iteration -> O(n^2) total
    process(item)
```

`.remove(0)` must shift all remaining elements left by one position.

**Manual fix — use reverse + `.pop()`, or use a proper queue:**

Option A — Reverse and pop from end:
```simple
queue.reverse()
while queue.len() > 0:
    val item = queue.pop()   # O(1) — removes from end
    process(item)
```

Option B — Use index cursor (no removal):
```simple
var i = 0
while i < queue.len():
    process(queue[i])
    i = i + 1
```

Option C — Use RingBuffer for true O(1) queue:
```simple
use std.collections.ring_buffer

val rb = ring_buffer_128()
rb.enqueue(item)
val item = rb.dequeue()      # O(1) via circular buffer
```

**Why the compiler cannot auto-fix:** Requires choosing a replacement strategy (reverse, index, ring buffer) that depends on usage context.

**Current compiler codebase:** No instances of `.remove(0)` in loops found.

---

### COLL004 — Loop-Invariant Method Call (MEDIUM)

**The problem:**
```simple
while i < data.len():        # .len() called every iteration
    process(data[i])
    i = i + 1
```

While `.len()` is O(1) (returns stored length field), calling it in every loop iteration adds unnecessary overhead from function dispatch.

**Manual fix — cache before loop:**
```simple
val data_len = data.len()
while i < data_len:
    process(data[i])
    i = i + 1
```

**Compiler auto-fix (MIR level):** The `collection_opt` pass hoists calls to known-pure methods (`len`, `is_empty`, `first`, `last`, `get`, `contains_key`) to the loop pre-header when all arguments are loop-invariant.

**Found in compiler codebase (30+ instances):**

| File | Lines | Context |
|------|-------|---------|
| `20.hir/hir_lowering/items.spl` | 38, 149, 157, 165, 173, 181, 189, 197, 205, 209, 254, 261 | HIR lowering loops |
| `20.hir/inference/unify.spl` | 55, 67, 85 | Type unification loops |
| `70.backend/linker/lib_smf_reader.spl` | 270 | Byte reading loop |
| `70.backend/linker/lib_smf_writer.spl` | 311 | Byte writing loop |

---

### COLL005 — Chained `.filter().filter()` (MEDIUM)

**The problem:**
```simple
val result = data.filter(\x: x > 0).filter(\x: x < 100)
# Two full passes over the data, two intermediate arrays
```

Each `.filter()` creates a new array and iterates all elements. Chaining two filters means two passes and two allocations.

**Manual fix — combine predicates:**
```simple
val result = data.filter(\x: x > 0 and x < 100)
# Single pass, single allocation
```

**Why the compiler cannot auto-fix:** Combining filter predicates requires understanding their semantics and ensuring no side effects. The predicates could reference different closures with captured state.

**Current compiler codebase:** No instances of chained `.filter().filter()` found.

---

## Runtime Internals: `.push()` vs `arr + [x]`

| Aspect | `.push()` (`spl_array_push`) | `arr + [x]` (`spl_array_concat`) |
|--------|------------------------------|----------------------------------|
| Mutation | In-place | Creates new array |
| Return value | Same array pointer | New array pointer |
| Time complexity | O(1) amortized | O(n+m) full copy |
| Memory | Single buffer, grows 2x | New allocation per call |
| Initial capacity | 16 elements | Exact size |
| Growth strategy | Exponential doubling | No growth |
| GC pressure | Low | High (temporary arrays) |

**Runtime source:** `src/runtime/runtime.c`
- `spl_array_push()` — lines 280-287
- `spl_array_concat()` — lines 289-303

---

## Available Data Structures

| Need | Use | Location |
|------|-----|----------|
| Fast membership test | `Dict<K, bool>` or `Set<T>` | `src/lib/nogc_sync_mut/src/set.spl` |
| FIFO queue | `RingBuffer` (fixed capacity) | `src/lib/nogc_async_mut_noalloc/collections/ring_buffer.spl` |
| Dynamic queue | `queue_enqueue` / `queue_dequeue` | `src/lib/common/queue/` |
| Ordered unique set | `Set<T>` with `.to_list()` | `src/lib/nogc_sync_mut/src/set.spl` |
| Hash map | `Dict<K, V>` (built-in) | Built into runtime |

---

## Optimization Passes

### Lint Pass (`src/compiler/35.semantics/lint/collection_patterns.spl`)

Detects all 5 patterns at the AST level during `build lint`. Walks function body statements, finds loops, checks for anti-patterns inside loop bodies.

Entry point: `check_collection_patterns(decl_indices: [i64]) -> [CollectionLintWarning]`

### MIR Optimizer Pass (`src/compiler/60.mir_opt/mir_opt/collection_opt.spl`)

Runs in the Speed and Aggressive optimization pipelines (after `loop_invariant_motion`). Transforms:
1. **Concat-to-push:** 3-instruction sliding window replacement in loop bodies
2. **Pure call hoisting:** Moves loop-invariant calls to known-pure methods before the loop

Factory: `create_collection_opt_pass() -> CollectionOptimization`

Registered in pipeline: `src/compiler/60.mir_opt/mir_opt/mod.spl`

---

## Recommendations

### For compiler contributors

1. **Always use `.push()`** instead of `arr = arr + [x]` when building arrays incrementally
2. **Cache `.len()`** before while loops: `val n = arr.len(); while i < n:`
3. **Use Dict for lookups** instead of array `.contains()` when the collection grows
4. **Combine filter predicates** into a single `.filter()` call

### For the compiler itself

The compiler already handles patterns 1 and 4 automatically in the MIR optimization pipeline. Patterns 2, 3, and 5 require fundamentally different data structures that cannot be inferred — these must be fixed in source code.

The lint pass warns about all 5 patterns at compile time, giving developers the opportunity to fix them before they become performance problems.
