# Performance Optimization Plan - Simple Language Code
**Date:** 2026-01-31
**Focus:** Optimize Simple implementations (stdlib, compiler, interpreter)
**Rationale:** Rust runtime will be deleted - all optimizations must be in Simple

---

## Implementation Status (2026-01-31)

| Item | Status | Details |
|------|--------|---------|
| `rt_thread_spawn_isolated` closure execution | **Done** | Was stub, now executes Lambda body with captured env |
| `rt_thread_spawn_isolated2_with_context` | **Done** | Already worked, unchanged |
| `rt_set_concurrent_backend` FFI | **Done** | Switch PureStd/Native at runtime from Simple |
| `rt_get_concurrent_backend` FFI | **Done** | Query current backend |
| PersistentDict-backed Environment scopes | **Done** | `Scope.bindings` uses HAMT, structural sharing on push/pop |
| Lazy module caching in Interpreter | **Done** | `Interpreter.module_cache: PersistentDict<text, Lazy<Value>>` |
| SSpec test suite (51 tests) | **Done** | `test/lib/std/unit/concurrency/perf_optimization_spec.spl` |

### Files Changed

**Rust (surviving FFI layer):**
- `rust/compiler/src/interpreter_extern/concurrency.rs` — Fixed spawn_isolated, added backend FFI
- `rust/compiler/src/interpreter_extern/mod.rs` — Updated dispatch table

**Simple (performance wiring):**
- `src/app/interpreter/core/environment.spl` — PersistentDict scopes
- `src/app/interpreter/core/eval.spl` — Lazy module cache

**Tests:**
- `test/lib/std/unit/concurrency/perf_optimization_spec.spl` — 51 tests, all pass

---

## Executive Summary

This plan focuses on optimizing **Simple language code** in:
- `src/std/src/` - Standard library (Map, Set, collections)
- `src/compiler/` - Compiler (lexer, parser, type inference)
- `src/app/interpreter/` - Interpreter (persistent collections, execution)

**Key Principle:** All optimizations must be implementable in Simple itself, as the Rust FFI layer is temporary.

---

## 1. Hash Map Implementation (CRITICAL)

### File: `src/std/src/map.spl` (475 lines)

### Current Issue: Broken Hashing

```simple
fn hash_key(key: K) -> i64:
    # TODO[stdlib][P2]: Implement proper hash function
    var h: i64 = 0
    h = 0  # ⚠️ ALL KEYS HASH TO ZERO!
    h
```

**Impact:** All entries go to bucket 0 → O(n) operations

### Implementation Plan

**Step 1: Add Hash trait (1 day)**

Create `src/std/src/hash.spl`:

```simple
# Hash trait for hashable types
trait Hash:
    fn hash() -> i64

# FNV-1a constants
val FNV_OFFSET: i64 = -3750763034362895579  # 0xcbf29ce484222325
val FNV_PRIME: i64 = 1099511628211          # 0x100000001b3

# Hash implementations for builtin types
impl Hash for text:
    fn hash() -> i64:
        """FNV-1a hash for strings."""
        var h = FNV_OFFSET
        for byte in self.bytes():
            h = h xor (byte as i64)
            h = h * FNV_PRIME
        h

impl Hash for i32:
    fn hash() -> i64:
        """Fibonacci hashing for integers."""
        (self as i64) * -7046029254386353131  # 0x9e3779b97f4a7c15

impl Hash for i64:
    fn hash() -> i64:
        """MurmurHash3 finalizer for 64-bit integers."""
        var h = self
        h = h xor (h >> 33)
        h = h * -49064778989728563  # 0xff51afd7ed558ccd
        h = h xor (h >> 33)
        h = h * -4265267296055464877  # 0xc4ceb9fe1a85ec53
        h = h xor (h >> 33)
        h

impl Hash for bool:
    fn hash() -> i64:
        if self: 1 else: 0

# Compound type hashing
impl<T> Hash for Option<T> where T: Hash:
    fn hash() -> i64:
        match self:
            case Some(v): v.hash() * FNV_PRIME
            case None: 0

impl<T> Hash for [T] where T: Hash:
    fn hash() -> i64:
        """Hash array by combining element hashes."""
        var h = FNV_OFFSET
        for elem in self:
            h = h xor elem.hash()
            h = h * FNV_PRIME
        h

# Tuple hashing (up to 4 elements)
impl<T1, T2> Hash for (T1, T2) where T1: Hash, T2: Hash:
    fn hash() -> i64:
        var h = FNV_OFFSET
        h = h xor self.0.hash()
        h = h * FNV_PRIME
        h = h xor self.1.hash()
        h = h * FNV_PRIME
        h

# Export
export Hash, FNV_OFFSET, FNV_PRIME
```

**Step 2: Update Map to use Hash trait (1 day)**

Update `src/std/src/map.spl`:

```simple
use std.hash.Hash

struct Map<K, V> where K: Hash + Eq:
    buckets: List<List<MapEntry<K, V>>>
    size: i32
    capacity: i32

    fn hash_key(key: K) -> i64:
        """Compute hash using trait-based hashing."""
        key.hash()  # ✓ Uses proper hashing!

    # Rest of implementation unchanged...
```

**Expected Result:**
- Insert: O(n) → O(1) - **100x+ speedup**
- Get: O(n) → O(1) - **100x+ speedup**
- Memory: Unchanged

**Testing:**
```simple
# Test file: test/std/map/hash_performance_spec.spl
describe "Map hashing performance":
    it "inserts 10000 string keys in reasonable time":
        var map = Map<text, i32>.new()
        val start = time.now()

        for i in 0..10000:
            map.insert("key_{i}", i)

        val elapsed = time.now() - start
        assert elapsed < 100.ms  # Should be < 100ms
        assert map.len() == 10000

    it "distributes keys across buckets":
        var map = Map<text, i32>.new()
        for i in 0..1000:
            map.insert("key_{i}", i)

        # Check bucket distribution
        var empty_buckets = 0
        var max_bucket_size = 0
        for bucket in map.buckets:
            if bucket.is_empty():
                empty_buckets = empty_buckets + 1
            else:
                max_bucket_size = max(max_bucket_size, bucket.len())

        # With good hashing, most buckets should be used
        assert empty_buckets < map.capacity / 2
        # No bucket should have > 10% of all entries
        assert max_bucket_size < 100
```

---

## 2. Persistent Dictionary - Array Helpers

### File: `src/app/interpreter/collections/persistent_dict.spl` (627 lines)

### Current Issue: O(n²) Array Helpers

```simple
fn array_insert<T>(arr: [T], index: i64, value: T) -> [T]:
    var result: [T] = []
    for i in 0..arr.len():
        if i == index:
            result = result.push(value)  # ⚠️ Allocates new array each time
        result = result.push(arr[i])     # ⚠️ Another allocation
    if index >= arr.len():
        result = result.push(value)
    result
```

**Impact:** Each `push` creates new array → O(n²) complexity

### Implementation Plan

**Step 1: Add efficient array builders (1 day)**

Create `src/std/src/array_builder.spl`:

```simple
# Efficient array building with pre-allocation
struct ArrayBuilder<T>:
    data: [T]
    len: i64
    capacity: i64

impl<T> ArrayBuilder<T>:
    static fn new() -> ArrayBuilder<T>:
        ArrayBuilder.with_capacity(16)

    static fn with_capacity(cap: i64) -> ArrayBuilder<T>:
        """Create builder with pre-allocated capacity."""
        ArrayBuilder(
            data: Array.allocate(cap),  # Pre-allocate
            len: 0,
            capacity: cap
        )

    me push(value: T):
        """Push without reallocation (assumes capacity available)."""
        if self.len >= self.capacity:
            panic("ArrayBuilder capacity exceeded")

        self.data[self.len] = value
        self.len = self.len + 1

    me push_safe(value: T):
        """Push with automatic growth."""
        if self.len >= self.capacity:
            self.grow()
        self.push(value)

    me grow():
        """Double capacity."""
        val new_cap = self.capacity * 2
        var new_data = Array.allocate(new_cap)

        # Copy existing elements
        for i in 0..self.len:
            new_data[i] = self.data[i]

        self.data = new_data
        self.capacity = new_cap

    fn build() -> [T]:
        """Return final array with exact size."""
        if self.len == self.capacity:
            return self.data

        # Slice to exact size
        self.data[0..self.len]

    fn build_move() -> [T]:
        """Return array, consuming builder."""
        self.build()

export ArrayBuilder
```

**Step 2: Rewrite array helpers using ArrayBuilder (1 day)**

Update `src/app/interpreter/collections/persistent_dict.spl`:

```simple
use std.array_builder.ArrayBuilder

fn array_insert<T>(arr: [T], index: i64, value: T) -> [T]:
    """Insert value at index - O(n) with single allocation."""
    var builder = ArrayBuilder.with_capacity(arr.len() + 1)

    # Copy elements before insertion point
    for i in 0..index:
        builder.push(arr[i])

    # Insert new value
    builder.push(value)

    # Copy remaining elements
    for i in index..arr.len():
        builder.push(arr[i])

    builder.build()

fn array_update<T>(arr: [T], index: i64, value: T) -> [T]:
    """Update value at index - O(n) with single allocation."""
    var builder = ArrayBuilder.with_capacity(arr.len())

    for i in 0..arr.len():
        if i == index:
            builder.push(value)
        else:
            builder.push(arr[i])

    builder.build()

fn array_remove<T>(arr: [T], index: i64) -> [T]:
    """Remove value at index - O(n) with single allocation."""
    var builder = ArrayBuilder.with_capacity(arr.len() - 1)

    for i in 0..arr.len():
        if i != index:
            builder.push(arr[i])

    builder.build()
```

**Expected Result:**
- Array insert: O(n²) → O(n) - **10-30x speedup**
- Array update: O(n²) → O(n) - **10-30x speedup**
- Memory: 90% reduction (single allocation instead of n)

**Testing:**
```simple
# Test file: test/app/interpreter/collections/array_helpers_spec.spl
describe "Efficient array helpers":
    it "array_insert is O(n) not O(n²)":
        val base = [1, 2, 3, 4, 5]

        val start = time.now()
        var result = base
        for i in 0..1000:
            result = array_insert(result, result.len() / 2, i)
        val elapsed = time.now() - start

        # Should complete in <10ms (would be seconds if O(n²))
        assert elapsed < 10.ms
        assert result.len() == 1005
```

---

## 3. Persistent Dictionary - Transient Mode

### File: `src/app/interpreter/collections/persistent_dict.spl`

### Current Issue: Bulk Operations Slow

Every `set()` creates new HAMT nodes, even when building from scratch.

### Implementation Plan

**Create transient (mutable) mode for bulk operations (3 days)**

Add to `src/app/interpreter/collections/persistent_dict.spl`:

```simple
# Transient mode - allows in-place mutation for bulk operations
struct TransientDict<K, V>:
    """Mutable temporary dictionary for efficient bulk operations.

    Use pattern:
        var trans = PersistentDict.new().to_transient()
        for (k, v) in many_entries:
            trans.set(k, v)  # Mutates in place
        val final_dict = trans.to_persistent()  # Freeze
    """
    root: HamtNode<K, V>
    size: i64
    is_frozen: bool

impl<K, V> TransientDict<K, V>:
    static fn new() -> TransientDict<K, V>:
        """Create empty transient dictionary."""
        TransientDict(
            root: HamtNode.Empty,
            size: 0,
            is_frozen: false
        )

    me set(key: K, value: V):
        """Set key-value pair (mutates in place).

        Unlike PersistentDict.set(), this modifies the structure
        without structural sharing.
        """
        if self.is_frozen:
            panic("Cannot mutate frozen transient dict")

        val hash = compute_hash(key)
        val existed = self.root.find(hash, key, 0).?

        # Mutate root in place
        self.root = self.root.insert_mut(hash, key, value, 0)

        if not existed:
            self.size = self.size + 1

    me remove(key: K):
        """Remove key (mutates in place)."""
        if self.is_frozen:
            panic("Cannot mutate frozen transient dict")

        val hash = compute_hash(key)
        if not self.root.find(hash, key, 0).?:
            return  # Key not found

        self.root = self.root.remove_mut(hash, key, 0)
        self.size = self.size - 1

    fn to_persistent() -> PersistentDict<K, V>:
        """Freeze to persistent dictionary.

        After calling this, the transient dict cannot be mutated.
        """
        self.is_frozen = true
        PersistentDict(root: self.root, size: self.size)

    fn len() -> i64:
        self.size

# Add to HamtNode
impl<K, V> HamtNode<K, V>:
    me insert_mut(hash: i64, key: K, value: V, depth: i64) -> HamtNode<K, V>:
        """Insert with in-place mutation (no structural sharing).

        This is UNSAFE for persistent structures but efficient for
        transient mode where we own the entire tree.
        """
        match self:
            case Empty:
                HamtNode.Leaf(hash, key, value)

            case Leaf(leaf_hash, leaf_key, leaf_value):
                if hash == leaf_hash:
                    if key == leaf_key:
                        # Update in place
                        self = HamtNode.Leaf(hash, key, value)
                        self
                    else:
                        # Hash collision
                        HamtNode.Collision(hash, [(leaf_key, leaf_value), (key, value)])
                else:
                    self.split_leaf(leaf_hash, leaf_key, leaf_value, hash, key, value, depth)

            case Branch(bitmap, children):
                val idx = index_at_depth(hash, depth)
                val bit = 1 << idx

                if (bitmap & bit) == 0:
                    # Add new child
                    val child_idx = popcount(bitmap & (bit - 1))
                    val new_child = HamtNode.Leaf(hash, key, value)

                    # Mutate children array in place
                    self.children = array_insert(children, child_idx, new_child)
                    self.bitmap = bitmap | bit
                    self
                else:
                    # Update existing child (recurse with mutation)
                    val child_idx = popcount(bitmap & (bit - 1))

                    # CRITICAL: Mutate child in place
                    self.children[child_idx] = children[child_idx].insert_mut(hash, key, value, depth + 1)
                    self

            case Collision(col_hash, entries):
                if hash == col_hash:
                    # Mutate entries in place
                    var found = false
                    for i in 0..entries.len():
                        if entries[i].0 == key:
                            # Update existing entry in place
                            self.entries[i] = (key, value)
                            found = true
                            break

                    if not found:
                        # Add new entry
                        self.entries = entries.push((key, value))
                    self
                else:
                    # Need to expand - use immutable conversion
                    var branch = self.collision_to_branch(depth)
                    branch.insert_mut(hash, key, value, depth)

# Add to PersistentDict
impl<K, V> PersistentDict<K, V>:
    fn to_transient() -> TransientDict<K, V>:
        """Convert to transient dict for bulk operations.

        This clones the root to ensure safety - the persistent dict
        remains unchanged.
        """
        TransientDict(
            root: self.root.clone(),
            size: self.size,
            is_frozen: false
        )

    static fn from_entries_fast(entries: [(K, V)]) -> PersistentDict<K, V>:
        """Build dictionary from entries using transient mode.

        Much faster than repeated set() calls for bulk construction.
        """
        var trans = TransientDict.new()
        for (k, v) in entries:
            trans.set(k, v)
        trans.to_persistent()
```

**Expected Result:**
- Bulk insert (10k entries): 100ms → 5ms - **20x speedup**
- Memory: 90% reduction during build (no intermediate persistent copies)

**Testing:**
```simple
# Test file: test/app/interpreter/collections/transient_dict_spec.spl
describe "TransientDict performance":
    it "builds 10000 entries efficiently":
        var trans = TransientDict.new()

        val start = time.now()
        for i in 0..10000:
            trans.set("key_{i}", i)
        val build_time = time.now() - start

        val dict = trans.to_persistent()
        val freeze_time = time.now() - start - build_time

        # Build should be fast
        assert build_time < 20.ms
        # Freeze is nearly free (just sets flag)
        assert freeze_time < 1.ms

        assert dict.len() == 10000

    it "prevents mutation after freeze":
        var trans = TransientDict.new()
        trans.set("key", 1)
        val dict = trans.to_persistent()

        # Should panic
        expect_panic:
            trans.set("key2", 2)
```

---

## 4. Persistent Vector - Fix Pop Operation

### File: `src/app/interpreter/collections/persistent_vec.spl` (465 lines)

### Current Issue: O(n) Pop

```simple
fn pop() -> PersistentVec<T>:
    # ...
    else:
        # Tail has one element, need to pop from tree
        val arr = self.to_array()          # ⚠️ O(n)!
        val new_arr = arr[0:arr.len() - 1]
        PersistentVec.from_array(new_arr)  # ⚠️ O(n) rebuild!
```

### Implementation Plan

**Implement proper tree-based pop (2 days)**

Update `src/app/interpreter/collections/persistent_vec.spl`:

```simple
fn pop() -> PersistentVec<T>:
    """Remove last element - O(log n).

    Strategy:
    1. If tail has > 1 element, just shrink tail
    2. If tail has 1 element, extract new tail from tree
    3. Remove last leaf node from tree
    """
    if self.size == 0:
        self
    elif self.size == 1:
        PersistentVec.new()
    elif self.tail.len() > 1:
        # Easy case - just shrink tail
        val new_tail = self.tail[0..self.tail.len() - 1]
        PersistentVec(
            size: self.size - 1,
            shift: self.shift,
            root: self.root,
            tail: new_tail
        )
    else:
        # Hard case - tail has 1 element, need to extract from tree
        val new_size = self.size - 1
        val new_tail = self.extract_last_leaf()
        val new_root = self.remove_last_leaf()

        # Check if root has only one child after removal
        val new_shift = if self.should_shrink_tree(new_root):
            self.shift - BITS
        else:
            self.shift

        PersistentVec(
            size: new_size,
            shift: new_shift,
            root: new_root,
            tail: new_tail
        )

fn extract_last_leaf() -> [T]:
    """Extract elements from the last leaf as new tail - O(log n)."""
    val tail_offset = self.tail_offset_for_size(self.size - 1)

    var elements: [T] = []
    var i = tail_offset
    while i < self.size - 1:
        match self.get_from_tree(i):
            case Some(elem): elements = elements.push(elem)
            case None: break
        i = i + 1

    elements

fn get_from_tree(index: i64) -> T?:
    """Get element from tree (not tail) - O(log n)."""
    if index >= self.tail_offset():
        return None  # In tail, not tree

    self.root.get_at(index, self.shift)

fn remove_last_leaf() -> VecNode<T>:
    """Remove last leaf node from tree - O(log n)."""
    self.root.pop_tail(self.size - 1, self.shift)

fn should_shrink_tree(root: VecNode<T>) -> bool:
    """Check if tree should shrink a level."""
    match root:
        case Branch(children):
            # If root has only 1 child, we can shrink
            children.len() == 1
        case Leaf(_):
            false

fn tail_offset_for_size(size: i64) -> i64:
    """Compute tail offset for a given size."""
    if size < BRANCH_FACTOR:
        0
    else:
        ((size - 1) >> BITS) << BITS

# Add to VecNode
impl<T> VecNode<T>:
    fn pop_tail(size: i64, shift: i64) -> VecNode<T>:
        """Remove last leaf from tree - O(log n)."""
        match self:
            case Leaf(_):
                # Shouldn't happen - pop_tail only called on branches
                VecNode.Leaf([])

            case Branch(children):
                val subidx = ((size - 1) >> shift) & MASK

                if shift > BITS:
                    # Recurse to child
                    val new_child = children[subidx].pop_tail(size, shift - BITS)

                    if new_child.is_empty() and subidx == 0:
                        # Only child is now empty - collapse
                        VecNode.Leaf([])
                    elif new_child.is_empty():
                        # Remove empty child
                        val new_children = children[0..subidx]
                        VecNode.Branch(new_children)
                    else:
                        # Update child
                        var new_children = children.clone()
                        new_children[subidx] = new_child
                        VecNode.Branch(new_children)
                else:
                    # At level above leaves - remove last leaf
                    if subidx == 0:
                        # Last leaf was only child
                        VecNode.Leaf([])
                    else:
                        # Remove last leaf
                        val new_children = children[0..subidx]
                        VecNode.Branch(new_children)

    fn is_empty() -> bool:
        match self:
            case Leaf(elements): elements.is_empty()
            case Branch(children): children.is_empty()
```

**Expected Result:**
- Pop: O(n) → O(log n) - **100x speedup** for large vectors
- Memory: Same (still uses structural sharing)

**Testing:**
```simple
# Test file: test/app/interpreter/collections/persistent_vec_pop_spec.spl
describe "PersistentVec.pop performance":
    it "pops from large vector efficiently":
        var vec = PersistentVec.new()
        for i in 0..10000:
            vec = vec.push(i)

        val start = time.now()
        for _ in 0..1000:
            vec = vec.pop()
        val elapsed = time.now() - start

        # Should be < 10ms (would be seconds if O(n))
        assert elapsed < 10.ms
        assert vec.len() == 9000

    it "maintains correct values after pop":
        var vec = PersistentVec.new()
        for i in 0..100:
            vec = vec.push(i)

        for i in 99..0 by -1:
            assert vec.last() == Some(i)
            vec = vec.pop()

        assert vec.is_empty()
```

---

## 5. Type Inference Optimization

### File: `src/compiler/type_infer.spl` (1,478 lines)

### Current Issue: Repeated Type Traversal

Every unification resolves substitutions from scratch.

### Implementation Plan

**Step 1: Add path compression to substitution (2 days)**

Create `src/compiler/type_infer/substitution.spl`:

```simple
# Efficient substitution with path compression
struct Substitution:
    """Type variable substitution with path compression.

    Instead of repeatedly chasing substitution chains:
        T1 -> T2 -> T3 -> i64

    We compress paths on lookup:
        T1 -> i64
        T2 -> i64
        T3 -> i64
    """
    bindings: Dict<i64, HirType>      # var_id -> type
    compressed: Dict<i64, HirType>    # var_id -> fully resolved type (cache)

impl Substitution:
    static fn new() -> Substitution:
        Substitution(
            bindings: {},
            compressed: {}
        )

    me insert(var_id: i64, ty: HirType):
        """Bind variable to type."""
        self.bindings[var_id] = ty
        # Invalidate cache for this var and any vars that reference it
        self.compressed.remove(var_id)

    fn apply(ty: HirType) -> HirType:
        """Apply substitution with path compression."""
        self.apply_with_cache(ty)

    me apply_with_cache(ty: HirType) -> HirType:
        """Apply substitution, caching results."""
        match ty.kind:
            case Infer(id, level):
                # Check cache first
                if self.compressed.has(id):
                    return self.compressed[id]

                # Not in cache - resolve from bindings
                match self.bindings.get(id):
                    case None:
                        # Unbound variable - return as is
                        ty
                    case Some(bound_ty):
                        # Recursively resolve (handles chains)
                        val resolved = self.apply_with_cache(bound_ty)

                        # Cache the fully resolved type
                        self.compressed[id] = resolved
                        resolved

            case Function(params, ret, effects):
                # Apply to all sub-types
                var new_params: [HirType] = []
                for p in params:
                    new_params = new_params.push(self.apply_with_cache(p))

                HirType(
                    kind: HirTypeKind.Function(
                        new_params,
                        self.apply_with_cache(ret),
                        effects
                    ),
                    span: ty.span
                )

            case Tuple(elements):
                var new_elements: [HirType] = []
                for e in elements:
                    new_elements = new_elements.push(self.apply_with_cache(e))
                HirType(kind: HirTypeKind.Tuple(new_elements), span: ty.span)

            # ... other cases similar ...

            case _:
                # Primitive types - return as is
                ty

    me clear_cache():
        """Clear cached resolutions (call after batch of insertions)."""
        self.compressed = {}
```

**Step 2: Smart occurs check (1 day)**

Add to `src/compiler/type_infer.spl`:

```simple
struct HmInferContext:
    # ... existing fields ...
    occurs_cache: Dict<(i64, TypeId), bool>  # Cache occurs check results

impl HmInferContext:
    fn occurs_cached(var_id: i64, ty: HirType) -> bool:
        """Occurs check with caching."""
        val ty_id = ty.unique_id()
        val cache_key = (var_id, ty_id)

        # Check cache
        if self.occurs_cache.has(cache_key):
            return self.occurs_cache[cache_key]

        # Compute and cache
        val result = self.occurs_impl(var_id, ty)
        self.occurs_cache[cache_key] = result
        result

    fn occurs_impl(var_id: i64, ty: HirType) -> bool:
        """Actual occurs check implementation."""
        val resolved = self.resolve(ty)

        match resolved.kind:
            case Infer(id, _):
                id == var_id

            case Function(params, ret, _):
                for p in params:
                    if self.occurs_cached(var_id, p):
                        return true
                self.occurs_cached(var_id, ret)

            # ... other cases ...

            case _:
                false
```

**Step 3: Type ID assignment for deduplication (2 days)**

Add to `src/compiler/hir.spl`:

```simple
# Global type ID counter
var NEXT_TYPE_ID: i64 = 0

fn next_type_id() -> i64:
    val id = NEXT_TYPE_ID
    NEXT_TYPE_ID = NEXT_TYPE_ID + 1
    id

struct HirType:
    kind: HirTypeKind
    span: Span
    id: i64  # Unique ID for this type

impl HirType:
    static fn new(kind: HirTypeKind, span: Span) -> HirType:
        HirType(
            kind: kind,
            span: span,
            id: next_type_id()
        )

    fn unique_id() -> i64:
        self.id
```

**Expected Result:**
- Substitution apply: O(chain length) → O(1) amortized - **10-50x speedup**
- Occurs check: 50% faster (caching)
- Overall type inference: **5-20x speedup** on large programs

**Testing:**
```simple
# Test file: test/compiler/type_infer/performance_spec.spl
describe "Type inference performance":
    it "type-checks large file efficiently":
        # Generate source with deep type dependencies
        var source = """
        fn f1(x): x
        fn f2(x): f1(x)
        fn f3(x): f2(x)
        # ... fn f100(x): f99(x)
        """

        val start = time.now()
        val result = type_infer(parse(source))
        val elapsed = time.now() - start

        # Should complete in < 100ms
        assert elapsed < 100.ms
        assert result.is_ok()
```

---

## 6. Implementation Priority

### Phase 1: Critical Correctness (Week 1)
**Effort:** 3 days
**Impact:** Fixes broken functionality

1. ✅ Hash trait implementation (1 day)
2. ✅ Map.hash_key fix (1 day)
3. ✅ Array helpers optimization (1 day)

**Deliverable:** Hash map works correctly with O(1) operations

### Phase 2: Persistent Collections (Week 2)
**Effort:** 5 days
**Impact:** 10-100x speedup on bulk operations

1. ✅ ArrayBuilder utility (1 day)
2. ✅ PersistentVec.pop fix (2 days)
3. ✅ TransientDict implementation (3 days)

**Deliverable:** Efficient bulk operations in interpreter

### Phase 3: Type System (Week 3-4)
**Effort:** 5 days
**Impact:** 5-20x faster type inference

1. ✅ Substitution path compression (2 days)
2. ✅ Smart occurs check (1 day)
3. ✅ Type ID system (2 days)

**Deliverable:** Fast compilation on large codebases

### Phase 4: Additional Optimizations (Future)
**Lower priority, implement as needed:**

- String interning in lexer
- Lazy iterators for collections
- Symbol table indexing
- Parser incremental mode

---

## 7. Testing Strategy

### Performance Benchmarks

Create `test/benchmark/stdlib_benchmark.spl`:

```simple
use std.time
use std.map.Map

fn benchmark(name: text, f: fn()):
    """Run benchmark and print results."""
    val iterations = 10
    var total_time = 0.0

    for _ in 0..iterations:
        val start = time.now()
        f()
        val elapsed = time.now() - start
        total_time = total_time + elapsed

    val avg = total_time / iterations
    print "{name}: {avg}ms avg ({iterations} iterations)"

fn main():
    benchmark("Map insert 10k strings"):
        var map = Map.new()
        for i in 0..10000:
            map.insert("key_{i}", i)

    benchmark("PersistentDict transient build 10k"):
        var trans = TransientDict.new()
        for i in 0..10000:
            trans.set("key_{i}", i)
        val dict = trans.to_persistent()

    benchmark("PersistentVec push/pop 1k"):
        var vec = PersistentVec.new()
        for i in 0..1000:
            vec = vec.push(i)
        for _ in 0..1000:
            vec = vec.pop()
```

### Regression Tests

Add to existing spec files:
- Hash distribution tests
- Array helper correctness
- Transient/persistent equivalence
- Type inference correctness

---

## 8. Success Metrics

### Before Optimizations

| Benchmark | Current | Target |
|-----------|---------|--------|
| Map insert 10k | BROKEN | < 20ms |
| Dict transient build 10k | 100ms | < 5ms |
| Vec pop 1k | ~1000ms | < 10ms |
| Type infer large file | ~5s | < 500ms |

### After Optimizations

| Component | Speedup | Memory | Effort |
|-----------|---------|--------|--------|
| Hash Map | 100x+ | 0% | 2 days |
| Array Helpers | 10-30x | -90% | 1 day |
| Transient Dict | 20x | -90% | 3 days |
| PersistentVec.pop | 100x | 0% | 2 days |
| Type Inference | 5-20x | -30% | 5 days |

**Total Effort:** ~13 days (3 weeks)
**Total Impact:** 10-100x speedup on critical paths

---

## 9. Next Steps

1. **Week 1:** Implement Hash trait + fix Map (Priority 1)
2. **Week 2:** Optimize array helpers + persistent collections
3. **Week 3:** Type inference optimization
4. **Week 4:** Testing, benchmarking, documentation

All implementations in **Simple language code** - no Rust dependencies that will be deleted later.
