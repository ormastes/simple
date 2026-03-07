# Library Variant: `nogc_async_immut` — Immutable Persistent Data Structures for Lock-Free Concurrency

**Date:** 2026-03-03
**Status:** Draft - Research & Architecture
**Prereqs:** `doc/design/lib_variant_architecture_plan.md`, `doc/guide/sync_async/async/nogc_async_mut_architecture.md`, `doc/design/gc_nogc_module_parity.md`

---

## 0) Problem Statement

The current library variant system has 5 groups organized along GC/async/mutation axes:

```
                    ┌───────────┬────────────┬────────────────────┐
                    │  sync_mut │ async_mut  │ async_mut_noalloc  │
┌───────────────────┼───────────┼────────────┼────────────────────┤
│ nogc (unique ptr) │ VARIANT 1 │ VARIANT 2  │ VARIANT 3          │
│ gc (gc ptr)       │     -     │ VARIANT 4  │         -          │
└───────────────────┴───────────┴────────────┴────────────────────┘
```

**Missing:** An immutable variant for concurrent access without locks. Current gaps:

1. **PersistentVec/PersistentDict use full-copy** — O(n) per mutation, no structural sharing. Unsuitable for concurrent workloads with frequent updates.
2. **Lock-free collections are mutable** — `nogc_async_mut/concurrent/collections.spl` provides CAS-based HashMap/BTreeMap, but these are mutable shared state requiring careful synchronization.
3. **No persistent data structures with structural sharing** — No HAMT, RRB-tree, or persistent trie. The `collections/__init__.spl` lists `RRBTree`, `ImmutableSet`, `Trie` as NOT YET IMPLEMENTED.
4. **Actors copy messages** — No efficient way to share large immutable snapshots between actors without full cloning.
5. **No CAS-based atoms** — No Clojure-style `atom.swap(fn(old) -> new)` for coordinated immutable state.

### Goal

Add a 6th library variant — `nogc_async_immut` — providing:
- **Persistent data structures** with O(log n) structural sharing (HAMT, RRB-tree, persistent trie)
- **Lock-free coordination** via CAS atoms, snapshots, and versioned references
- **Zero-copy message passing** for actors using shared immutable references
- **Functional async combinators** (pure pipelines over futures without mutable state)

---

## 1) Research: How Other Languages Do This

### 1.1 Language Comparison

| Language | Approach | Default | Thread Safety | Key Structure |
|----------|----------|---------|---------------|---------------|
| **Scala** | 3 packages: `collection`, `.immutable`, `.mutable` | Immutable | By design | Vector (32-way tree) |
| **Rust** | Single collections + wrapper types (`Arc<T>`) | Immutable (borrow checker) | Compile-time | `im` crate (HAMT + RRB) |
| **Clojure** | Persistent structures + structural sharing | Immutable | Lock-free | HAMT, PersistentVector |
| **Kotlin** | `kotlinx.collections.immutable` (separate lib) | Mutable stdlib | Immutable layer | PersistentList/Map/Set |
| **Haskell** | Language-enforced purity, IO monad for mutation | Immutable | Type-system | Data.Map (balanced tree) |

### 1.2 Structural Sharing (Clojure Model)

The key insight from Clojure: persistent data structures share unchanged subtrees between versions.

```
Original vector [A, B, C, D, E, F, G, H] as 2-level tree:

         Root
        /    \
    [A,B,C,D] [E,F,G,H]

After set(index=5, value=F'):

         Root'             Root (old, still valid)
        /    \            /    \
    [A,B,C,D] [E,F',G,H]  [A,B,C,D] [E,F,G,H]
    ^^^^^^^^^              ^^^^^^^^^
    shared!                (original untouched)
```

- **Update cost:** O(log₃₂ n) — copy only the path from root to modified leaf
- **Memory:** Shared subtrees mean ~4 nodes copied per update (for 1M elements)
- **Branching factor 32:** Keeps tree depth ≤ 7 for collections up to 32^7 (~34 billion)

### 1.3 Key Data Structures

| Structure | Use Case | Lookup | Update | Append |
|-----------|----------|--------|--------|--------|
| **HAMT** (Hash Array Mapped Trie) | Map/Set | O(log₃₂ n) ≈ O(1) | O(log₃₂ n) | N/A |
| **RRB-Tree** (Relaxed Radix Balanced) | Vector | O(log₃₂ n) | O(log₃₂ n) | O(log₃₂ n) |
| **Persistent Trie** | String-keyed map | O(k) key length | O(k) | N/A |
| **Cons List** | Stack, LIFO | O(n) | O(1) prepend | O(1) prepend |
| **Persistent Red-Black Tree** | Sorted map/set | O(log n) | O(log n) | O(log n) |

### 1.4 Coordination Primitives (Clojure Atoms + Kotlin Builders)

**Atoms** — CAS-based mutable references to immutable values:
```simple
# Atom holds a PersistentMap, updated via swap()
val state = atom(persistent_map_empty())
state.swap(\old: old.set("key", "value"))  # CAS retry loop
val snapshot = state.deref()                # Read is always consistent
```

**Builders** — Mutable batch construction, then freeze:
```simple
val vec = persistent_vec_builder()
    .push(1).push(2).push(3)
    .build()  # Returns immutable PersistentVec
```

---

## 2) Architecture

### 2.1 Updated Variant Matrix

```
                    ┌───────────┬─────────────┬────────────┬────────────────────┐
                    │  sync_mut │ async_immut  │ async_mut  │ async_mut_noalloc  │
┌───────────────────┼───────────┼─────────────┼────────────┼────────────────────┤
│ nogc (unique ptr) │ VARIANT 1 │ VARIANT NEW │ VARIANT 2  │ VARIANT 3          │
│ gc (gc ptr)       │     -     │      -      │ VARIANT 4  │         -          │
└───────────────────┴───────────┴─────────────┴────────────┴────────────────────┘
```

### 2.2 Dependency Hierarchy

```
common (pure, no IO, no pointers)
  ├── nogc_sync_mut (blocking IO, unique ptrs)
  │     ├── nogc_async_immut (persistent structures, lock-free)  ← NEW
  │     │     └── nogc_async_mut can import from nogc_async_immut
  │     └── nogc_async_mut (async IO, actors, channels)
  │           ├── nogc_async_mut_noalloc (baremetal)
  │           └── gc_async_mut (GC + ML)
```

**Why between sync_mut and async_mut?**
- Needs `AtomicI64` and CAS from `nogc_sync_mut/atomic.spl`
- Does NOT need async runtime (futures, event loop) — immutable structures are inherently thread-safe
- `nogc_async_mut` actors can import persistent structures for zero-copy message snapshots

### 2.3 Import Resolution (Profile: `nogc_async_immut`)

```
use std.persistent_vec  → lib/nogc_async_immut/persistent_vec/
use std.fs              → lib/nogc_sync_mut/fs/  (parent)
use std.math            → lib/common/math/       (grandparent)
```

### 2.4 Design Principles

> **Principle 1: No `var`, no `me`.**
> All public types are immutable. Every "mutation" returns a new version. Methods use `fn name(self)`, never `me name()`.

> **Principle 2: Structural sharing by default.**
> Updates copy O(log n) nodes, not O(n). Old and new versions coexist safely.

> **Principle 3: Lock-free coordination via CAS atoms.**
> Shared mutable state is an `Atom<T>` — a CAS reference to an immutable `T`. No Mutex/RwLock needed.

> **Principle 4: Builder pattern for batch construction.**
> Transient/mutable builders for efficient batch construction, then `.build()` to freeze.

---

## 3) Data Model

### 3.1 Core Persistent Data Structures

#### 3.1.1 HAMT — Hash Array Mapped Trie (Map & Set)

```simple
# Internal node representation (tuple-based, matching existing tree conventions)
# Node types:
#   Empty     = nil
#   Leaf      = (hash: i64, key: K, value: V)
#   Branch    = (bitmap: i64, children: [HamtNode])
#   Collision = (hash: i64, entries: [(K, V)])

struct PersistentMap<K, V>:
    root: HamtNode
    size: i64
    hash_fn: fn(K) -> i64

    fn get(key: K) -> V?
    fn set(key: K, value: V) -> PersistentMap<K, V>     # Returns new map
    fn remove(key: K) -> PersistentMap<K, V>             # Returns new map
    fn contains(key: K) -> bool
    fn merge(other: PersistentMap<K, V>) -> PersistentMap<K, V>
    fn keys() -> [K]
    fn values() -> [V]
    fn entries() -> [(K, V)]
    fn map_values(f: fn(V) -> V2) -> PersistentMap<K, V2>
    fn filter(f: fn(K, V) -> bool) -> PersistentMap<K, V>
    fn fold(init: A, f: fn(A, K, V) -> A) -> A

struct PersistentSet<T>:
    inner: PersistentMap<T, ()>
    fn add(item: T) -> PersistentSet<T>
    fn remove(item: T) -> PersistentSet<T>
    fn contains(item: T) -> bool
    fn union(other: PersistentSet<T>) -> PersistentSet<T>
    fn intersection(other: PersistentSet<T>) -> PersistentSet<T>
    fn difference(other: PersistentSet<T>) -> PersistentSet<T>
```

**Implementation details:**
- 32-way branching (5 bits per level from hash)
- Bitmap compression: only allocate children that exist (popcount for index)
- Hash collision nodes for keys with identical hashes
- Depth ≤ 7 for 32-bit hashes (13 for 64-bit)

#### 3.1.2 RRB-Tree — Persistent Vector

```simple
# Relaxed Radix Balanced Tree
# Branch factor: 32 (matching Clojure/Scala)
# Node = leaf [T; 32] or branch [Node; 32] with size table

struct PersistentVec<T>:
    root: RrbNode
    tail: [T]          # Optimization: last partial leaf held separately
    size: i64
    shift: i64         # Tree depth * 5 (bits per level)

    fn get(index: i64) -> T?
    fn set(index: i64, value: T) -> PersistentVec<T>
    fn push(value: T) -> PersistentVec<T>
    fn pop() -> PersistentVec<T>
    fn slice(start: i64, end: i64) -> PersistentVec<T>
    fn concat(other: PersistentVec<T>) -> PersistentVec<T>  # O(log n) via RRB
    fn map(f: fn(T) -> T2) -> PersistentVec<T2>
    fn filter(f: fn(T) -> bool) -> PersistentVec<T>
    fn fold(init: A, f: fn(A, T) -> A) -> A
    fn take(n: i64) -> PersistentVec<T>
    fn drop(n: i64) -> PersistentVec<T>
```

**Implementation details:**
- Tail optimization: appends to partial tail buffer without tree traversal (amortized O(1))
- Size tables for relaxed nodes enable O(log n) concatenation (vs O(n) for strict radix)
- Transient mode for batch construction (mutable in-place until `.build()`)

#### 3.1.3 Persistent Sorted Map (Red-Black Tree)

```simple
# Persistent red-black tree (immutable, path-copying)
# Reuses existing red_black_tree/ patterns from common/

struct PersistentSortedMap<K, V>:
    root: RbNode
    size: i64
    compare: fn(K, K) -> i64

    fn get(key: K) -> V?
    fn set(key: K, value: V) -> PersistentSortedMap<K, V>
    fn remove(key: K) -> PersistentSortedMap<K, V>
    fn min_key() -> K?
    fn max_key() -> K?
    fn range(from: K, to: K) -> [(K, V)]
    fn floor(key: K) -> (K, V)?     # Greatest key ≤ given
    fn ceiling(key: K) -> (K, V)?   # Smallest key ≥ given
```

#### 3.1.4 Persistent Trie (String-Keyed Map)

```simple
# Prefix tree for text keys — O(k) operations where k = key length

struct PersistentTrie<V>:
    root: TrieNode
    size: i64

    fn get(key: text) -> V?
    fn set(key: text, value: V) -> PersistentTrie<V>
    fn remove(key: text) -> PersistentTrie<V>
    fn keys_with_prefix(prefix: text) -> [text]
    fn longest_prefix(query: text) -> text?
```

### 3.2 Lock-Free Coordination Primitives

#### 3.2.1 Atom — CAS Reference to Immutable Value

```simple
# Thread-safe mutable reference to an immutable value
# Uses compare-and-swap for lock-free updates

struct Atom<T>:
    _value_ptr: i64     # Atomic pointer to current value
    _version: AtomicI64  # Monotonic version counter

    fn deref() -> T                              # Read current value (always consistent)
    fn swap(f: fn(T) -> T) -> T                  # CAS loop: apply f, retry on conflict
    fn reset(new_value: T) -> T                  # Unconditional set
    fn compare_and_set(expected: T, new_value: T) -> bool  # Single CAS attempt
    fn version() -> i64                          # Current version number

# Factory
fn atom(initial: T) -> Atom<T>
```

**Implementation:** Uses `AtomicI64` from `nogc_sync_mut/atomic.spl`. The `swap()` method:
1. Read current value
2. Apply function to get new value
3. CAS (compare old pointer, set new pointer)
4. On failure: re-read and retry (spin loop with backoff)

#### 3.2.2 Ref — Transactional Reference (STM-lite)

```simple
# Software Transactional Memory — coordinated multi-ref updates
# Simpler than full STM: only supports swap-style updates

struct Ref<T>:
    _atom: Atom<T>
    _validator: fn(T) -> bool    # Optional validation function

    fn deref() -> T
    fn swap(f: fn(T) -> T) -> Result<T, text>  # Validates before commit
```

#### 3.2.3 VersionedSnapshot — MVCC-style Reads

```simple
# Multi-Version Concurrency Control for read-heavy workloads
# Readers get a consistent snapshot; writer publishes new versions

struct VersionedSnapshot<T>:
    _atom: Atom<(version: i64, data: T)>

    fn read() -> (version: i64, data: T)          # Snapshot read
    fn write(f: fn(T) -> T) -> i64                 # Returns new version
    fn read_at(version: i64) -> T?                 # Historical read (if retained)
```

### 3.3 Builder Pattern (Transients)

```simple
# Mutable builder for efficient batch construction
# Internally mutates, then freezes into persistent structure

struct PersistentVecBuilder<T>:
    _items: [T]    # Mutable during construction

    fn push(value: T) -> PersistentVecBuilder<T>
    fn push_all(values: [T]) -> PersistentVecBuilder<T>
    fn build() -> PersistentVec<T>    # Freeze into immutable

struct PersistentMapBuilder<K, V>:
    _entries: [(K, V)]

    fn set(key: K, value: V) -> PersistentMapBuilder<K, V>
    fn set_all(entries: [(K, V)]) -> PersistentMapBuilder<K, V>
    fn build() -> PersistentMap<K, V>

# Factory functions
fn persistent_vec_builder() -> PersistentVecBuilder<T>
fn persistent_map_builder() -> PersistentMapBuilder<K, V>
```

### 3.4 Functional Async Combinators

```simple
# Pure async pipelines — no mutable state

fn async_map(future: Future<T>, f: fn(T) -> U) -> Future<U>
fn async_flat_map(future: Future<T>, f: fn(T) -> Future<U>) -> Future<U>
fn async_filter(futures: [Future<T>], f: fn(T) -> bool) -> Future<[T]>
fn async_fold(futures: [Future<T>], init: A, f: fn(A, T) -> A) -> Future<A>
fn async_zip(a: Future<T>, b: Future<U>) -> Future<(T, U)>
fn async_race(futures: [Future<T>]) -> Future<T>   # First to complete
fn async_all(futures: [Future<T>]) -> Future<[T]>  # All must complete
```

---

## 4) Directory Structure

```
src/lib/nogc_async_immut/
  __init__.spl                    # Re-exports all public types

  # --- Core Persistent Collections ---
  persistent_vec/
    __init__.spl                  # PersistentVec<T> API
    rrb_node.spl                  # RRB-tree node operations
    transient.spl                 # PersistentVecBuilder (mutable batch)

  persistent_map/
    __init__.spl                  # PersistentMap<K, V> API
    hamt_node.spl                 # HAMT node operations (bitmap, popcount)
    collision.spl                 # Hash collision handling
    transient.spl                 # PersistentMapBuilder

  persistent_set/
    __init__.spl                  # PersistentSet<T> (wraps PersistentMap)

  persistent_sorted_map/
    __init__.spl                  # PersistentSortedMap<K, V>
    rb_node.spl                   # Persistent red-black tree nodes
    path_copy.spl                 # Path-copying rebalance

  persistent_trie/
    __init__.spl                  # PersistentTrie<V> (string keys)
    trie_node.spl                 # Trie node operations

  persistent_list/
    __init__.spl                  # Cons list — O(1) prepend, O(n) access

  # --- Coordination Primitives ---
  atom/
    __init__.spl                  # Atom<T> — CAS reference
    cas.spl                       # CAS loop with exponential backoff

  ref/
    __init__.spl                  # Ref<T> — validated transactional reference

  versioned/
    __init__.spl                  # VersionedSnapshot<T> — MVCC reads

  # --- Functional Combinators ---
  combinators/
    __init__.spl                  # async_map, async_fold, async_zip, etc.
    pipeline.spl                  # Pipe-based composition for persistent transforms

  # --- Integration ---
  actor_snapshot/
    __init__.spl                  # Zero-copy actor message snapshots
```

**Estimated size:** ~25-30 files, ~5,000-8,000 lines

---

## 5) Key Decisions

### D1: Branching Factor = 32

**Rationale:** Matches Clojure (32) and Scala (32). Balances tree depth (≤7 for 32-bit hashes) against node size. 32 fits in a cache line on modern CPUs. Bit manipulation uses 5-bit chunks (`hash >> (level * 5) & 0x1F`).

### D2: Tuple-Based Nodes (Not Classes)

**Rationale:** All existing tree structures in `common/` use tuples: `(value, left, right, height)` for AVL, `(value, color, left, right, parent)` for red-black. Following this convention for consistency and performance (no vtable overhead).

### D3: Atom Uses AtomicI64 (Not Mutex)

**Rationale:** CAS-based atoms are lock-free and wait-free for readers. Writers may retry on contention, but no thread ever blocks. This matches Clojure's atom semantics. Uses existing `AtomicI64.compare_exchange()` from `nogc_sync_mut/atomic.spl`.

### D4: No Full STM (Software Transactional Memory)

**Rationale:** Full STM (coordinated multi-ref transactions) adds significant complexity. Start with single-ref atoms. Multi-ref coordination can be added later via snapshot isolation if needed.

### D5: Builders Are Mutable (Intentionally)

**Rationale:** Following Kotlin's `persistentListOf().builder().apply { ... }.build()` pattern. Builders use `var` and `me` internally for performance. The `.build()` method freezes state and returns an immutable persistent structure. This is the only place `me` methods appear in this library.

### D6: PersistentSet Wraps PersistentMap

**Rationale:** Following Scala/Clojure pattern — `PersistentSet<T>` is `PersistentMap<T, ()>`. Avoids duplicating HAMT logic. Minor memory overhead (unit values) is negligible.

---

## 6) Implementation Plan — Agent Teams

### Phase 0: Foundation (HAMT + Atom)
**Duration:** Core data structures that everything else builds on.
**Agent assignments:**

| Task | Agent | Files | Description |
|------|-------|-------|-------------|
| 0.1 HAMT node operations | **code** | `hamt_node.spl`, `collision.spl` | Bitmap indexing, popcount, node split/merge, collision lists |
| 0.2 PersistentMap API | **code** | `persistent_map/__init__.spl` | get/set/remove/merge/filter/fold over HAMT |
| 0.3 PersistentSet | **code** | `persistent_set/__init__.spl` | Thin wrapper over PersistentMap |
| 0.4 Atom (CAS reference) | **code** | `atom/__init__.spl`, `atom/cas.spl` | AtomicI64-based CAS loop, exponential backoff |
| 0.5 Tests: HAMT | **test** | `test/unit/lib/persistent_map_spec.spl` | get/set/remove, collision handling, 1000-element stress |
| 0.6 Tests: Atom | **test** | `test/unit/lib/atom_spec.spl` | swap, compare_and_set, concurrent contention |

**Parallel execution:**
- Tasks 0.1-0.4 can run in parallel (code agents)
- Tasks 0.5-0.6 depend on 0.1-0.4 (test agents wait)

### Phase 1: RRB-Tree + Builders
**Agent assignments:**

| Task | Agent | Files | Description |
|------|-------|-------|-------------|
| 1.1 RRB node operations | **code** | `rrb_node.spl` | 32-way branching, tail buffer, size tables |
| 1.2 PersistentVec API | **code** | `persistent_vec/__init__.spl` | get/set/push/pop/slice/concat/map/filter |
| 1.3 Builders (transients) | **code** | `persistent_vec/transient.spl`, `persistent_map/transient.spl` | Mutable batch construction + freeze |
| 1.4 Tests: PersistentVec | **test** | `test/unit/lib/persistent_vec_spec.spl` | structural sharing verification, concat, 10K elements |
| 1.5 Tests: Builders | **test** | `test/unit/lib/persistent_builder_spec.spl` | batch construction, freeze semantics |

**Parallel execution:**
- 1.1 + 1.2 sequential (1.2 depends on 1.1)
- 1.3 can start after Phase 0 PersistentMap is done
- Tests after implementations

### Phase 2: Sorted Structures + Trie
**Agent assignments:**

| Task | Agent | Files | Description |
|------|-------|-------|-------------|
| 2.1 Persistent Red-Black Tree | **code** | `persistent_sorted_map/rb_node.spl`, `path_copy.spl` | Path-copying insert/delete with rebalance |
| 2.2 PersistentSortedMap API | **code** | `persistent_sorted_map/__init__.spl` | range queries, floor/ceiling, min/max |
| 2.3 PersistentTrie | **code** | `persistent_trie/__init__.spl`, `trie_node.spl` | Prefix tree for text keys |
| 2.4 Persistent Cons List | **code** | `persistent_list/__init__.spl` | O(1) prepend cons list |
| 2.5 Tests: SortedMap + Trie | **test** | `test/unit/lib/persistent_sorted_map_spec.spl`, `persistent_trie_spec.spl` | Range queries, prefix search, ordering |

**Parallel execution:** All of 2.1-2.4 can run in parallel.

### Phase 3: Coordination + Combinators
**Agent assignments:**

| Task | Agent | Files | Description |
|------|-------|-------|-------------|
| 3.1 Ref (validated atom) | **code** | `ref/__init__.spl` | Validator function, error on invalid state |
| 3.2 VersionedSnapshot (MVCC) | **code** | `versioned/__init__.spl` | Version-stamped reads, historical snapshots |
| 3.3 Async combinators | **code** | `combinators/__init__.spl`, `pipeline.spl` | async_map/fold/zip/race/all |
| 3.4 Actor snapshot integration | **code** | `actor_snapshot/__init__.spl` | Zero-copy persistent message snapshots for actors |
| 3.5 Tests: Coordination | **test** | `test/unit/lib/ref_spec.spl`, `versioned_snapshot_spec.spl` | Validation, MVCC reads, concurrent snapshots |
| 3.6 Tests: Combinators | **test** | `test/unit/lib/async_combinators_spec.spl` | Pipeline composition, race semantics |

### Phase 4: Module Resolver + Documentation
**Agent assignments:**

| Task | Agent | Files | Description |
|------|-------|-------|-------------|
| 4.1 Module resolver update | **code** | `src/compiler/99.loader/module_resolver/` | Add `nogc_async_immut` to resolution chain |
| 4.2 Profile integration | **code** | `src/compiler/80.driver/driver_types.spl` | New profile enum variant, import fallback order |
| 4.3 Parity tracking | **docs** | `doc/design/gc_nogc_module_parity.md` | Update parity table with new variant |
| 4.4 Architecture doc | **docs** | `doc/guide/nogc_async_immut_architecture.md` | Module map, design decisions, usage examples |
| 4.5 Integration tests | **test** | `test/integration/persistent_collections_spec.spl` | Cross-module usage, actor+persistent interop |

---

## 7) Trait Hierarchy

Shared traits live in `common/` so all variants can implement them:

```simple
# src/lib/common/traits/persistent.spl

trait PersistentCollection<T>:
    fn len() -> i64
    fn is_empty() -> bool
    fn to_list() -> [T]

trait PersistentSequence<T> with PersistentCollection:
    fn get(index: i64) -> T?
    fn set(index: i64, value: T) -> Self
    fn push(value: T) -> Self
    fn pop() -> Self
    fn first() -> T?
    fn last() -> T?

trait PersistentAssociative<K, V> with PersistentCollection:
    fn get(key: K) -> V?
    fn set(key: K, value: V) -> Self
    fn remove(key: K) -> Self
    fn contains(key: K) -> bool
    fn keys() -> [K]
    fn values() -> [V]
    fn entries() -> [(K, V)]
```

---

## 8) Performance Targets

| Operation | PersistentVec | PersistentMap | Existing PersistentVec (copy) |
|-----------|---------------|---------------|-------------------------------|
| get(i) | O(log₃₂ n) | O(log₃₂ n) | O(1) |
| set(i, v) | O(log₃₂ n) | O(log₃₂ n) | **O(n)** |
| push(v) | O(1) amortized | N/A | **O(n)** |
| concat | O(log₃₂ n) | O(n + m) | **O(n + m)** |
| Memory per update | ~4-7 nodes | ~4-7 nodes | **Full copy** |

**Key win:** For a 1M-element collection, `set()` copies ~7 nodes (~224 slots) instead of 1M elements. This is the structural sharing advantage.

---

## 9) Migration from Existing Collections

### 9.1 From `common/collections/persistent_vec.spl`

```simple
# Before (full-copy, O(n) per mutation):
val vec = persistent_vec_new()
val vec2 = persistent_vec_push(vec, 42)  # Copies entire array

# After (structural sharing, O(log n) per mutation):
val vec = PersistentVec.empty()
val vec2 = vec.push(42)  # Copies ~4 nodes
```

### 9.2 From `nogc_async_mut/concurrent/collections.spl`

```simple
# Before (mutable CAS HashMap, shared state):
val map = concurrent_hashmap_new()
concurrent_hashmap_insert(map, "key", "value")  # Mutates in-place

# After (immutable HAMT, no locking needed):
val map = PersistentMap.empty()
val map2 = map.set("key", "value")  # Returns new version
# Both map and map2 are valid, can be read by any thread
```

---

## 10) Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| Generics not fully working in interpreter | High | Test with compiled mode; use `i64`/`text` specializations as fallback |
| CAS loop starvation under high contention | Medium | Exponential backoff with jitter; fall back to Mutex for >100 retries |
| Structural sharing memory leaks | Medium | Reference counting on shared nodes; periodic compaction |
| HAMT bitmap/popcount complexity | Low | Well-documented algorithm; port from Clojure reference implementation |
| Path-copying red-black tree complexity | Medium | Existing `red_black_tree/` in common/ as reference; thorough testing |

---

## 11) Open Questions

1. **Should `PersistentVec` replace `common/collections/persistent_vec.spl`?**
   - **Recommendation:** Yes, but keep the old one as `SimpleVec` for backward compat during transition.

2. **Should atoms support watchers (notify on change)?**
   - **Recommendation:** Phase 2 feature. Start with simple swap/deref.

3. **Should builders be thread-safe?**
   - **Recommendation:** No. Builders are single-threaded construction tools. Use atoms for concurrent state.

4. **HAMT hash function: use runtime hash or custom?**
   - **Recommendation:** Use `rt_hash_text()` / `rt_hash_i64()` FFI for hash generation. Provide `hash_fn` parameter for custom hashers.

---

## Cross-References

- [Library Variant Architecture Plan](lib_variant_architecture_plan.md) — Parent architecture
- [GC/NoGC Module Parity](gc_nogc_module_parity.md) — Parity tracking
- [Async Architecture](../guide/sync_async/async/nogc_async_mut_architecture.md) — Async runtime details
- [Baremetal Resources](baremetal_async_resources_v0.3.md) — NoAlloc patterns
- [Manual Memory Safety Plan](../plan/manual_memory_safety_plan.md) — Pointer type system
