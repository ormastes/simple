# Simple Language Performance Optimization Plan

**Date:** 2026-01-26
**Status:** All Phases Complete ✅
**Focus:** Simple code optimizations (self-hosted compiler)

## Implementation Status

| Phase | Description | Status | Files |
|-------|-------------|--------|-------|
| 1 | Symbol Interning | ✅ Complete | `core/symbol.spl`, `core/environment.spl` |
| 2 | Persistent Collections | ✅ Complete | `collections/persistent_dict.spl`, `collections/persistent_vec.spl`, `collections/persistent_symbol_table.spl` |
| 3 | Actor Heap Isolation | ✅ Complete | `async_runtime/actor_heap.spl`, `async_runtime/mailbox.spl`, `async_runtime/actor_scheduler.spl` |
| 4 | Reference-Counted Binaries | ✅ Complete | `memory/refc_binary.spl`, `memory/message_transfer.spl` |
| 5 | Lazy Evaluation | ✅ Complete | `lazy/lazy_val.spl`, `lazy/lazy_seq.spl` |

## Executive Summary

Since Simple is self-hosting (compiler in `simple/compiler/`), optimizations should be done in **Simple code**, not Rust. This plan focuses on Erlang-inspired patterns for message-oriented, conflict-free structures.

**Key insight:** Simple's actor model + immutable values = opportunity for Erlang-style optimizations without thread conflicts.

---

## Architecture: Self-Hosted Compiler

```
simple/compiler/
├── lexer.spl          # Tokenization
├── parser.spl         # AST generation
├── hir.spl            # High-level IR (1713 lines) ← Symbol tables here
├── resolve.spl        # Method resolution (UFCS)
├── type_infer.spl     # Type inference
├── mir.spl            # Mid-level IR
├── codegen.spl        # Code generation
└── driver.spl         # Compilation driver
```

**Current patterns in Simple code:**
- `Dict<text, T>` for symbol tables → text key hashing overhead
- `[T].push(item)` returns new array → immutable but copies
- Pattern matching everywhere → good for optimization
- Actor-based runtime → per-actor isolation possible

---

## Erlang Optimizations Applicable to Simple

### 1. Per-Actor Heap Isolation (No GC Pause)

**Erlang approach:**
> "GC is per process. If GC occurs in a process with a 20K heap, then the collector only touches that 20K and collection time is imperceptible." — [Erlang GC](https://prog21.dadgum.com/16.html)

**Apply to Simple:**

```simple
# Each actor gets isolated heap - GC only affects that actor
actor spawn:
    val local_data = process_messages()  # In actor's private heap
    # GC here doesn't block other actors

# Current: All actors share heap → global GC pauses
# Target: Per-actor heaps → microsecond GC
```

**Implementation in Simple:**
```simple
# Actor with pre-sized heap (Erlang optimization)
fn spawn_with_heap_size(size: i64, body: fn()):
    """Spawn actor with initial heap size.

    If heap >= expected data size, no GC during actor lifetime.
    """
    rt_actor_spawn_with_heap(body, size)
```

### 2. Reference-Counted Large Binaries (Zero-Copy)

**Erlang approach:**
> "Binary terms > 64 bytes are not stored in process private heap. They are called Refc Binary and stored in a large Shared Heap accessible by all processes." — [Erlang Efficiency Guide](https://www.erlang.org/doc/system/eff_guide_processes)

**Apply to Simple:**

```simple
# Small values: copied between actors (< 64 bytes)
# Large values: reference-counted, shared (>= 64 bytes)

struct LargeBinary:
    """Off-heap binary with reference counting."""
    data: *u8
    len: i64
    refcount: AtomicI64  # Shared across actors

# Message passing:
#   - Small: deep copy (fast for small data)
#   - Large: share reference (zero-copy)
fn send(actor: Actor, msg: Value):
    if msg.size() < 64:
        rt_actor_send_copy(actor, msg)      # Deep copy
    else:
        rt_actor_send_ref(actor, msg)       # Share ref
```

### 3. Structural Sharing (Persistent Data Structures)

**Key insight from Erlang/Clojure:**
> "Nodes that don't change are shared. Only a single tree branch is traversed or updated when accessing a specific tree element." — [Persistent Data Structures](https://www.augustl.com/blog/2019/you_have_to_know_about_persistent_data_structures/)

**Current Simple pattern (inefficient):**
```simple
# hir.spl - Symbol table using Dict<text, Symbol>
struct SymbolTable:
    symbols: Dict<i64, Symbol>      # Linear rehash on grow
    scopes: Dict<i64, Scope>        # Full copy on "update"
```

**Proposed: HAMT (Hash Array Mapped Trie)**
```simple
# Persistent Dict with structural sharing
struct PersistentDict<K, V>:
    """Hash Array Mapped Trie - O(log32 n) operations."""
    root: Node<K, V>
    size: i64

impl PersistentDict<K, V>:
    fn set(key: K, value: V) -> PersistentDict<K, V>:
        """Return new dict with key set. Shares unchanged nodes."""
        val new_root = self.root.update(key.hash(), key, value)
        PersistentDict(root: new_root, size: self.size + 1)

    fn get(key: K) -> V?:
        """O(log32 n) lookup - effectively O(1) for realistic sizes."""
        self.root.find(key.hash(), key)

# Usage in SymbolTable:
struct SymbolTable:
    symbols: PersistentDict<SymbolId, Symbol>  # O(1) update, sharing
```

**Benefits:**
- Updates: O(log32 n) ≈ O(7) for billions of entries
- Memory: Only changed path is copied (~7 nodes)
- Safe sharing: Immutable = no conflicts between actors

### 4. Symbol Interning (SymbolId over text)

**Current (hir.spl):**
```simple
# Already using SymbolId! Good.
struct SymbolId:
    id: i64

struct SymbolTable:
    symbols: Dict<i64, Symbol>  # i64 key = fast hash
```

**But environment.spl still uses text:**
```simple
# environment.spl:17 - Using String keys
struct Scope:
    bindings: Dict<String, Binding>  # String = slow hash, memory
```

**Proposed: Use SymbolId everywhere**
```simple
# Interned symbols for all identifiers
struct Scope:
    bindings: Dict<SymbolId, Binding>  # i64 = fast hash, 8 bytes

# Global intern table
static SYMBOLS: SymbolInterner = SymbolInterner.new()

struct SymbolInterner:
    strings: [text]
    map: Dict<text, SymbolId>

impl SymbolInterner:
    me intern(s: text) -> SymbolId:
        if self.map[s].?:
            self.map[s]
        else:
            val id = SymbolId(id: self.strings.len())
            self.strings = self.strings.push(s)
            self.map[s] = id
            id

    fn resolve(id: SymbolId) -> text:
        self.strings[id.id]
```

**Benefits:**
- Comparison: O(n) string → O(1) integer
- Hashing: String hash → direct use of id
- Memory: Many "foo" → one "foo" + SymbolId(42)

### 5. Reductions-Based Fair Scheduling

**Erlang approach:**
> "A reduction is a counter per process which increments with each function call, capped at approximately 2000. Every 2000 function calls, the schedulers preempt the current task." — [Erlang Scheduler](https://blog.appsignal.com/2024/04/23/deep-diving-into-the-erlang-scheduler.html)

**Apply to Simple actors:**
```simple
# Reduction counting for fair actor scheduling
struct ActorContext:
    reductions: i64
    max_reductions: i64  # Default: 2000

fn run_actor(ctx: ActorContext):
    while true:
        val msg = recv()
        process(msg)
        ctx.reductions = ctx.reductions + 1

        if ctx.reductions >= ctx.max_reductions:
            ctx.reductions = 0
            yield_to_scheduler()  # Let other actors run
```

**Benefits:**
- No actor monopolizes CPU
- Predictable latency
- Fair message processing

### 6. Off-Heap Messages

**Erlang approach:**
> "Off-heap messages slightly more expensive but very neat for processes that receive a ton of messages. GC doesn't need to consider unmatched messages." — [Message Passing](https://www.erlang.org/blog/message-passing/)

**Apply to Simple:**
```simple
# Messages stored outside actor heap
struct OffHeapMessage:
    data: *u8           # Raw bytes
    size: i64
    next: *OffHeapMessage

struct ActorMailbox:
    head: *OffHeapMessage
    tail: *OffHeapMessage
    count: i64

# recv() moves message into actor heap only when matched
fn recv() -> Value:
    val msg = mailbox.pop()  # Off-heap
    msg.materialize()        # Copy into actor heap
```

**Benefits:**
- GC skips unread messages
- Fast message queue operations
- Memory-efficient for high-throughput actors

### 7. Lazy Evaluation (Scala/Erlang-style)

**Proposed syntax:**
```simple
# Lazy val - evaluated on first access
lazy val expensive = compute_heavy_thing()

# Lazy collections (infinite sequences)
lazy fn naturals(start: i64):
    yield start
    yield from naturals(start + 1)

val evens = naturals(0).filter(\x: x % 2 == 0).take(10)
```

**Implementation:**
```simple
enum LazyState<T>:
    Pending(thunk: fn() -> T)
    Evaluating
    Ready(value: T)

struct Lazy<T>:
    state: LazyState<T>

impl Lazy<T>:
    fn force() -> T:
        match self.state:
            case Ready(v): v
            case Evaluating: panic("Cycle in lazy evaluation")
            case Pending(thunk):
                self.state = LazyState.Evaluating
                val result = thunk()
                self.state = LazyState.Ready(result)
                result
```

---

## Simple Code Optimization Targets

### Priority 1: Symbol Interning (10-15% speedup)

| File | Change |
|------|--------|
| `environment.spl:17` | `Dict<String, Binding>` → `Dict<SymbolId, Binding>` |
| `hir.spl:152` | `Dict<text, SymbolId>` → `Dict<SymbolId, SymbolId>` |
| All string keys | Replace with interned SymbolId |

### Priority 2: Persistent Collections (20-30% memory)

| Current | Proposed |
|---------|----------|
| `Dict<K, V>` | `PersistentDict<K, V>` (HAMT) |
| `[T]` | `PersistentVec<T>` (RRB-tree) |
| `Environment.scopes` | Shared scope chain |

### Priority 3: Actor Heap Isolation (GC latency)

| Feature | Benefit |
|---------|---------|
| Per-actor heap | No global GC pause |
| Pre-sized heap | Zero GC for short-lived actors |
| Off-heap messages | GC skips mailbox |

### Priority 4: Large Value Sharing (memory, throughput)

| Size | Strategy |
|------|----------|
| < 64 bytes | Deep copy (fast) |
| >= 64 bytes | Reference counted, shared |

---

## Implementation Plan

### Phase 1: Symbol Interning (Simple code)

```simple
# Add to simple/lib/core/symbol.spl
struct SymbolInterner:
    strings: [text]
    map: Dict<text, SymbolId>

impl SymbolInterner:
    static fn global() -> &SymbolInterner:
        """Get global interner."""
        ...

    me intern(s: text) -> SymbolId:
        ...

# Update environment.spl
struct Scope:
    bindings: Dict<SymbolId, Binding>  # Changed from String
```

### Phase 2: Persistent Dict (Simple code)

```simple
# Add to simple/lib/collections/persistent.spl
struct PersistentDict<K, V>:
    """Hash Array Mapped Trie with 32-way branching."""
    root: HamtNode<K, V>
    size: i64

enum HamtNode<K, V>:
    Empty
    Leaf(hash: i64, key: K, value: V)
    Branch(bitmap: i32, children: [HamtNode<K, V>])
    Collision(hash: i64, entries: [(K, V)])

impl PersistentDict<K, V>:
    fn set(key: K, value: V) -> PersistentDict<K, V>:
        """O(log32 n) update with structural sharing."""
        ...

    fn get(key: K) -> V?:
        """O(log32 n) lookup."""
        ...
```

### Phase 3: Actor Heap Isolation (Runtime)

```simple
# Expose from Rust runtime as FFI
extern fn rt_actor_spawn_with_heap(body: fn(), heap_size: i64) -> Actor

# Simple wrapper
fn spawn_actor(body: fn(), opts: SpawnOptions) -> Actor:
    if opts.heap_size.?:
        rt_actor_spawn_with_heap(body, opts.heap_size.unwrap())
    else:
        rt_actor_spawn(body)
```

### Phase 4: Reference-Counted Binaries

```simple
# Large binary type with refcounting
extern class ReferenceBinary:
    static fn new(data: [u8]) -> ReferenceBinary
    fn as_slice() -> &[u8]
    fn len() -> i64

# Transparent for message passing
fn send(actor: Actor, msg: Value):
    match msg:
        case Binary(b) if b.len() >= 64:
            rt_actor_send_ref(actor, b)  # Share ref
        case _:
            rt_actor_send_copy(actor, msg)  # Copy
```

---

## Expected Performance Gains

| Optimization | Memory | Throughput | Latency |
|--------------|--------|------------|---------|
| Symbol interning | -15% | +10% | - |
| Persistent Dict | -20% | +5% | - |
| Per-actor heap | - | - | -90% GC pause |
| Refcounted binaries | -30% | +50% msg | - |
| Off-heap messages | -10% | +20% | -50% GC |
| Reductions scheduling | - | - | Predictable |

**Combined estimate:** 30-50% improvement in memory-bound workloads, predictable latency for actor systems.

---

## Key Erlang Lessons

1. **Process isolation is key:** Each actor = separate heap = separate GC
2. **Immutability enables sharing:** No locks needed for read-only data
3. **Large binaries are special:** Reference count instead of copy
4. **Fair scheduling matters:** Reductions prevent starvation
5. **Off-heap for throughput:** Messages outside heap = fast GC

---

## References

- [Erlang Garbage Collection](https://hamidreza-s.github.io/erlang%20garbage%20collection%20memory%20layout%20soft%20realtime/2015/08/24/erlang-garbage-collection-details-and-why-it-matters.html)
- [Erlang Scheduler Details](https://blog.appsignal.com/2024/04/23/deep-diving-into-the-erlang-scheduler.html)
- [BEAM Message Passing](https://www.erlang.org/blog/message-passing/)
- [Erlang Efficiency Guide - Processes](https://www.erlang.org/doc/system/eff_guide_processes)
- [Persistent Data Structures](https://www.augustl.com/blog/2019/you_have_to_know_about_persistent_data_structures/)
- [HAMT - Ideal Hash Trees](https://en.wikipedia.org/wiki/Hash_array_mapped_trie)
- [Immer C++ Persistent Structures](https://github.com/arximboldi/immer)
- [Structural Sharing in Immutable.js](https://medium.com/@dtinth/immutable-js-persistent-data-structures-and-structural-sharing-6d163fbd73d2)

---

## Completed Implementations

### Phase 1: Symbol Interning ✅

**Files created:**
- `src/app/interpreter/core/symbol.spl` - SymbolId, SymbolInterner, global intern table
- `src/app/interpreter/core/symbol_spec.spl` - Test specifications

**Files modified:**
- `src/app/interpreter/core/environment.spl` - Dict<String, Binding> → Dict<i64, Binding>
- `src/app/interpreter/core/eval.spl` - Uses intern() for variable names
- `src/app/interpreter/expr/calls.spl` - Uses define_str()
- `src/app/interpreter/control/loops.spl` - Uses define_str()
- `src/app/interpreter/control/match.spl` - Uses define_str()
- `src/app/interpreter/async_runtime/actors.spl` - Uses define_str()

**Key types:**
```simple
struct SymbolId:
    id: i64

struct SymbolInterner:
    strings: [text]
    map: Dict<text, SymbolId>

fn intern(s: text) -> SymbolId
fn resolve(id: SymbolId) -> text?
```

### Phase 2: Persistent Collections ✅

**Files created:**
- `src/app/interpreter/collections/__init__.spl` - Module exports
- `src/app/interpreter/collections/persistent_dict.spl` - HAMT implementation
- `src/app/interpreter/collections/persistent_vec.spl` - RRB-tree implementation
- `src/app/interpreter/collections/persistent_symbol_table.spl` - Immutable symbol table
- `src/app/interpreter/collections/persistent_dict_spec.spl` - Dict tests
- `src/app/interpreter/collections/persistent_vec_spec.spl` - Vec tests

**Key types:**
```simple
# HAMT-based dictionary - O(log32 n) operations
struct PersistentDict<K, V>:
    root: HamtNode<K, V>
    size: i64

# RRB-tree based vector - O(log32 n) random access, O(1) append
struct PersistentVec<T>:
    size: i64
    shift: i64
    root: VecNode<T>
    tail: [T]

# Immutable symbol table using PersistentDict
struct PersistentSymbolTable:
    symbols: PersistentDict<i64, SymbolEntry>
    scopes: PersistentDict<i64, PersistentScope>
```

### Phase 3: Actor Heap Isolation ✅

**Files created:**
- `src/app/interpreter/async_runtime/actor_heap.spl` - Per-actor heap management
- `src/app/interpreter/async_runtime/mailbox.spl` - Off-heap message queues
- `src/app/interpreter/async_runtime/actor_scheduler.spl` - Reductions-based scheduling
- `src/app/interpreter/async_runtime/actor_heap_spec.spl` - Heap tests
- `src/app/interpreter/async_runtime/mailbox_spec.spl` - Mailbox tests
- `src/app/interpreter/async_runtime/actor_scheduler_spec.spl` - Scheduler tests

**Files modified:**
- `src/app/interpreter/async_runtime/__init__.spl` - Added exports for new modules

**Key types:**
```simple
# Per-actor heap with generational GC
struct ActorHeap:
    config: HeapConfig
    stats: HeapStats
    young_generation: HeapRegion
    old_generation: HeapRegion?

# Off-heap message queue with priorities
struct Mailbox:
    config: MailboxConfig
    high_queue: [MessageRef]
    normal_queue: [MessageRef]
    low_queue: [MessageRef]

# Reductions-based fair scheduler
struct ActorScheduler:
    config: SchedulerConfig
    actors: Dict<i64, ActorContext>
    run_queues: [RunQueue]

# Actor runtime context
struct ActorContext:
    id: i64
    heap: ActorHeap
    mailbox: Mailbox
    reductions_left: i64
```

**Features:**
- Per-actor heap isolation (Erlang-style GC)
- Generational garbage collection (young/old generations)
- Off-heap message storage (GC doesn't scan unread messages)
- Priority-based message queues (High/Normal/Low)
- Selective receive (pattern matching out-of-order)
- Reductions-based fair scheduling (2000 reductions/timeslice)
- Work stealing for load balancing
- Actor linking and monitoring (fault tolerance)

### Phase 4: Reference-Counted Binaries ✅

**Files created:**
- `src/app/interpreter/memory/__init__.spl` - Module exports
- `src/app/interpreter/memory/refc_binary.spl` - Reference-counted binaries and shared heap
- `src/app/interpreter/memory/message_transfer.spl` - Intelligent message transfer
- `src/app/interpreter/memory/refc_binary_spec.spl` - Binary tests
- `src/app/interpreter/memory/message_transfer_spec.spl` - Transfer tests

**Key types:**
```simple
# Reference to shared binary (lightweight handle)
struct BinaryRef:
    id: i64             # Unique binary ID
    offset: i64         # Offset in shared heap
    length: i64         # Length of data

# Reference-counted binary in shared heap
struct RefcBinary:
    id: i64
    refcount: i64       # Atomic reference count
    length: i64
    data_ptr: i64       # Pointer to actual data

# Shared heap for all actors
struct SharedHeap:
    binaries: Dict<i64, RefcBinary>
    config: SharedHeapConfig
    stats: SharedHeapStats

# Intelligent message wrapper
enum ValueWrapper:
    InlineNil           # Small values (copied)
    InlineInt(i64)
    InlineSmallText(text)
    SharedRef(BinaryRef)  # Large values (zero-copy)
    Composite([ValueWrapper])

# Message transfer with size-based strategy
struct MessageTransfer:
    shared_heap: SharedHeap
    stats: TransferStats
    strategy: CopyStrategy
```

**Features:**
- Threshold-based strategy (64 bytes): small=copy, large=share
- Reference counting for automatic cleanup
- Sub-binaries for slicing without copying
- Pinning to prevent GC collection
- Defragmentation for shared heap
- Statistics tracking (sharing ratio, efficiency)
- Integration with actor mailboxes

**Erlang inspiration:**
> "Binary terms > 64 bytes are not stored in process private heap.
>  They are called Refc Binary and stored in a large Shared Heap
>  accessible by all processes."
> — Erlang Efficiency Guide

**Benefits:**
- Zero-copy for large messages (>= 64 bytes)
- Reduced memory usage (one copy instead of N)
- Faster message passing for large payloads
- Automatic cleanup via reference counting

### Phase 5: Lazy Evaluation ✅

**Files created:**
- `src/app/interpreter/lazy/__init__.spl` - Module exports
- `src/app/interpreter/lazy/lazy_val.spl` - Lazy values with memoization
- `src/app/interpreter/lazy/lazy_seq.spl` - Lazy/infinite sequences
- `src/app/interpreter/lazy/lazy_val_spec.spl` - Lazy value tests
- `src/app/interpreter/lazy/lazy_seq_spec.spl` - Lazy sequence tests

**Key types:**
```simple
# Lazy value state
enum LazyState<T>:
    Pending         # Not yet evaluated
    Evaluating      # Currently evaluating (cycle detection)
    Ready(value: T) # Evaluated and cached
    Failed(error: text)

# Lazy value with memoization
struct Lazy<T>:
    state: LazyState<T>
    thunk: fn() -> T

impl Lazy<T>:
    static fn new(thunk: fn() -> T) -> Lazy<T>
    me force() -> Result<T, LazyError>  # Evaluate and cache
    fn map<U>(f: fn(T) -> U) -> Lazy<U>  # Lazy transformation
    fn flat_map<U>(f: fn(T) -> Lazy<U>) -> Lazy<U>

# Memoization cache
struct Memo<K, V>:
    cache: Dict<K, Lazy<V>>

# Lazy sequence node
enum LazySeqNode<T>:
    Empty
    Cons(head: T, tail: Lazy<LazySeqNode<T>>)

# Lazy/infinite sequences
struct LazySeq<T>:
    node: Lazy<LazySeqNode<T>>

impl LazySeq<T>:
    static fn iterate(seed: T, f: fn(T) -> T) -> LazySeq<T>  # Infinite
    fn map<U>(f: fn(T) -> U) -> LazySeq<U>  # Lazy
    fn filter(p: fn(T) -> bool) -> LazySeq<T>  # Lazy
    fn take(n: i64) -> LazySeq<T>  # Lazy
    fn to_array() -> [T]  # Force evaluation

# Standard infinite sequences
fn naturals() -> LazySeq<i64>      # 0, 1, 2, 3, ...
fn fibonacci() -> LazySeq<i64>    # 0, 1, 1, 2, 3, 5, 8, ...
fn primes() -> LazySeq<i64>       # 2, 3, 5, 7, 11, ...
```

**Features:**
- Lazy values with automatic memoization
- Cycle detection (prevents infinite loops)
- Lazy transformations (map, flat_map, filter, zip)
- Infinite sequences (naturals, fibonacci, primes)
- Short-circuit evaluation (find, exists, take)
- Memoization cache for expensive pure functions
- Statistics tracking (hit rate, evaluation time)

**Scala/Haskell inspiration:**
> "Lazy evaluation means expressions are not evaluated until their values
>  are needed. Combined with memoization, each expression is evaluated
>  at most once."
> — Scala Documentation

**Example usage:**
```simple
# Lazy value - computed only when needed
val expensive = Lazy.new(\: heavy_computation())
val result = expensive.force()  # Computed here, cached

# Infinite sequence - only computed elements are stored
val evens = naturals()
    .filter(\x: x % 2 == 0)
    .take(10)
    .to_array()
# [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]

# Memoization for recursive functions
val fib_memo = Memo<i64, i64>.new()
fn fib(n: i64) -> i64:
    fib_memo.get_or_compute(n, \:
        if n <= 1: n
        else: fib(n - 1) + fib(n - 2)
    )
```

**Benefits:**
- Deferred computation: expensive operations only run when needed
- Memory efficient: only computed elements stored
- Composable: all operations are lazy until forced
- Safe: cycle detection prevents infinite loops

### Integration: Performance Module ✅

**Files created:**
- `src/app/interpreter/perf/__init__.spl` - Unified module exports
- `src/app/interpreter/perf/perf_config.spl` - Configuration profiles
- `src/app/interpreter/perf/perf_stats.spl` - Statistics collection
- `src/app/interpreter/perf/benchmark.spl` - Benchmarking framework
- `src/app/interpreter/perf/perf_spec.spl` - Test specifications
- `src/app/interpreter/perf/example_benchmarks.spl` - Example benchmarks

**Unified Configuration:**
```simple
# Predefined profiles
val config = PerfProfile.Production.to_config()
val config = PerfProfile.LowLatency.to_config()
val config = PerfProfile.MemoryConstrained.to_config()

# Custom configuration
val config = PerfConfig.default()
    .with_actor_heap_size(1024 * 1024)
    .with_reductions(4000)
    .with_large_binary_threshold(128)
```

**Performance Profiles:**

| Profile | Use Case | Key Settings |
|---------|----------|--------------|
| Development | Fast iteration | Single-threaded, detailed stats |
| Testing | Reproducible | Deterministic, bounded mailboxes |
| Production | Balanced | All optimizations, no stats overhead |
| LowLatency | Response time | Small heaps, 500 reductions |
| HighThroughput | Batch processing | Large heaps, 8000 reductions |
| MemoryConstrained | Limited RAM | Small caches, aggressive sharing |
| ActorHeavy | Many actors | Per-actor GC, priority mailboxes |

**Statistics Collection:**
```simple
val stats = collect_stats()
print(stats.summary())

# Access specific component
val lazy_stats = stats.get_component("lazy")
print("Hit rate: {lazy_stats.get_metric(\"hit_rate\")}")
```

**Benchmarking:**
```simple
val result = run_benchmark("dict_insert", 1000, \:
    var dict = PersistentDict.new()
    for i in 0..100:
        dict = dict.set(i, i * 2)
)
print(result.summary())

# Compare implementations
val comparison = compare_benchmarks(baseline, candidate)
print(comparison.summary())  # "candidate: 2.0x faster"
```

---

## Summary

All 5 phases plus integration are complete:

| Phase | Optimization | Files Created | Key Benefit |
|-------|-------------|---------------|-------------|
| 1 | Symbol Interning | 2 | O(1) string comparison |
| 2 | Persistent Collections | 5 | Structural sharing |
| 3 | Actor Heap Isolation | 6 | Per-actor GC |
| 4 | Reference-Counted Binaries | 4 | Zero-copy large values |
| 5 | Lazy Evaluation | 4 | Deferred computation |
| - | Integration/Perf Module | 5 | Unified config/stats/benchmarks |

**Total: 26 implementation files + test specifications**

**Expected combined benefits:**
- 30-50% memory reduction (structural sharing, interning)
- 10-20% throughput improvement (zero-copy, caching)
- 90% reduction in GC pause times (per-actor heaps)
- Predictable latency (reductions-based scheduling)
- Efficient infinite data processing (lazy evaluation)
