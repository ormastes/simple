# Structural Sharing Implementation

**Feature #1386:** Structural sharing for immutable collections

## Overview

Structural sharing is an optimization technique for immutable data structures where multiple versions of a collection share common structure. This allows efficient "modifications" that only copy the changed parts while reusing unchanged portions.

## Implementation Status

The persistent list implementation (`persistent_list.spl`) already uses structural sharing:

### How It Works

```simple
# Original list
let list1 = PList.of([1, 2, 3])
# Memory: Cons(1, Cons(2, Cons(3, Empty)))

# Prepend creates new head, shares tail
let list2 = list1.prepend(0)
# Memory: Cons(0, <shared reference to list1>)
# list1 and list2 share the [1, 2, 3] structure
```

### Benefits

1. **Memory Efficiency**: O(1) memory for prepend operations
2. **Time Efficiency**: O(1) time for prepend operations
3. **Immutability**: Both versions remain immutable
4. **Safety**: No aliasing issues with immutable data

### Performance Characteristics

| Operation | Time | Space | Sharing |
|-----------|------|-------|---------|
| prepend | O(1) | O(1) | Full tail sharing |
| append | O(n) | O(n) | No sharing |
| map | O(n) | O(n) | No sharing (transforms) |
| filter | O(n) | O(k) | Partial sharing possible |
| tail | O(1) | O(0) | Full sharing |

## Advanced Techniques

### Copy-on-Write (COW)

For more complex structures like vectors, we can use copy-on-write:

```simple
struct COWVector[T]:
    data: Rc[Vector[T]]  # Reference-counted vector
    
    fn modify(mut self, index: usize, value: T):
        # Only copy if multiple references exist
        if Rc.strong_count(self.data) > 1:
            self.data = Rc.new(self.data.clone())
        self.data.set(index, value)
```

### Path Copying

For tree structures (RRB-Tree, B-Tree), only copy the path from root to modified leaf:

```
Original Tree:        After Modification:
    A                     A'
   / \                   /  \
  B   C                 B'   C (shared)
 / \                   / \
D   E                 D'  E (shared)
```

Only nodes A', B', D' are new. C and E are shared.

### Reference Counting

Simple's GC handles reference counting automatically:

```simple
enum PList[T]:
    Empty
    Cons(head: T, tail: PList[T])  # tail is automatically ref-counted

# When list2 = list1.prepend(0):
# - New Cons node created
# - tail reference to list1 increments ref count
# - When list1 goes out of scope, ref count decrements
# - Nodes only freed when ref count reaches 0
```

## Integration with GC

The garbage collector handles structural sharing transparently:

1. **Allocation**: Nodes allocated in GC heap
2. **Reference Tracking**: GC tracks references between nodes
3. **Deallocation**: Nodes freed when no longer referenced
4. **No User Intervention**: Automatic memory management

## Future Optimizations

### RRB-Tree (Relaxed Radix Balanced Tree)

For better append performance:
- O(log n) append instead of O(n)
- O(log n) random access
- O(log n) updates
- Full structural sharing

### Persistent Vector

Array-like structure with:
- O(log₃₂ n) ≈ O(1) access/update
- Efficient structural sharing
- 32-way branching tree

### Persistent HashMap

Hash array mapped trie (HAMT):
- O(log₃₂ n) operations
- Structural sharing on updates
- Memory-efficient

## Example: Before/After

### Without Structural Sharing (Mutable)

```simple
let mut list = [1, 2, 3]
list.insert(0, 0)  # Modifies in place
# Can't access original [1, 2, 3]
# Risk of aliasing bugs
```

### With Structural Sharing (Immutable)

```simple
let list1 = PList.of([1, 2, 3])
let list2 = list1.prepend(0)
# Both list1 and list2 available
# No aliasing possible
# Efficient memory usage through sharing
```

## Implementation Guidelines

### When to Use Structural Sharing

✅ **Good for:**
- Frequent small modifications
- Need multiple versions
- Immutability required
- Undo/redo functionality

❌ **Not ideal for:**
- Random access heavy workloads
- Frequent large updates
- Single version needed
- Performance-critical tight loops

### Design Principles

1. **Immutability First**: Never modify existing nodes
2. **Share Aggressively**: Reuse unchanged structure
3. **Path Copy**: Only copy modified path
4. **Let GC Handle It**: Don't manually manage references

## Testing

```simple
fn test_structural_sharing():
    let list1 = PList.of([1, 2, 3])
    let list2 = list1.prepend(0)
    
    # Verify both versions exist
    assert list1.to_list() == [1, 2, 3]
    assert list2.to_list() == [0, 1, 2, 3]
    
    # Verify sharing (both point to same tail)
    assert list2.tail().unwrap() == list1
```

## References

- Okasaki, Chris. "Purely Functional Data Structures" (1996)
- Bagwell, Phil. "Ideal Hash Trees" (2001)
- Clojure's PersistentVector implementation
- Scala's Vector implementation

## Status

- ✅ Basic structural sharing: Implemented in PList
- ✅ GC integration: Automatic via Simple's GC
- 📋 Advanced structures: RRB-Tree, HAMT (planned)
- 📋 Performance benchmarks: Needed

## Conclusion

Structural sharing is already implemented in the persistent list (`PList`) through Simple's automatic memory management. The GC handles reference counting and deallocation, making structural sharing both efficient and transparent to users.

Future work includes implementing more advanced persistent data structures (RRB-Tree, persistent Vector, HAMT) for better performance characteristics while maintaining the same structural sharing benefits.
