# Collection Literals in Simple

## Overview

Simple supports three built-in collection literal syntaxes:

- **Arrays**: `[1, 2, 3]`
- **Dicts**: `{"key": "value"}`
- **Sets**: `s{1, 2, 3}` (new in v0.5.1)

## Set Literals

Create sets using `s{...}` syntax:

```simple
val nums = s{1, 2, 3}          # Set<i64>
val words = s{"hello", "world"} # Set<text>
val empty: Set<i64> = s{}      # Empty set (type annotation required)
```

### Automatic Deduplication

Sets automatically remove duplicate elements:

```simple
val nums = s{1, 2, 2, 3}  # Only {1, 2, 3}
check nums.len() == 3
```

### Type Inference

The element type is inferred from the first element:

```simple
val nums = s{1, 2, 3}     # Set<i64>
val mixed = s{1, "two"}   # ERROR: mixed types not allowed
```

For empty sets, you must provide a type annotation:

```simple
val empty: Set<i64> = s{}
```

### Set Operations

Sets support standard set operations:

```simple
val a = s{1, 2, 3}
val b = s{2, 3, 4}

# Union: elements in either set
val union = a.union(b)        # {1, 2, 3, 4}

# Intersection: elements in both sets
val common = a.intersect(b)   # {2, 3}

# Difference: elements in a but not b
val diff = a.diff(b)          # {1}

# Symmetric difference: elements in either but not both
val sym = a.sym_diff(b)       # {1, 4}
```

### Membership Testing

```simple
val nums = s{1, 2, 3}

if nums.has(2):
    print "Found 2"

if nums.has(5):
    print "Not reached"
```

### Iteration

```simple
val nums = s{1, 2, 3}

# Convert to list (order not guaranteed)
val list = nums.to_list()

# Map over elements
val doubled = nums.map(\x: x * 2)  # s{2, 4, 6}

# Filter elements
val evens = nums.filter(\x: x % 2 == 0)

# For-each iteration
for num in nums.to_list():
    print num
```

## Configuration

Customize literal syntax via `simple.sdn`:

### Default Configuration

```sdn
parser:
  literals:
    # Arrays: [1, 2, 3]
    array:
      enabled: true
      prefix: ""
      brackets: "[]"

    # Dicts: {"key": "value"}
    dict:
      enabled: true
      prefix: ""
      brackets: "{}"

    # Sets: s{1, 2, 3}
    set:
      enabled: true
      prefix: "s"
      brackets: "{}"
```

### Custom Prefix

Change the set literal prefix:

```sdn
parser:
  literals:
    set:
      prefix: "set"  # Use set{1, 2, 3} instead of s{1, 2, 3}
```

Usage:

```simple
val nums = set{1, 2, 3}  # With custom prefix
```

## Custom Collection Types (Advanced)

Define custom literals for your own types:

### Configuration

```sdn
parser:
  literals:
    custom:
      sorted_set:
        enabled: true
        prefix: "sorted"
        brackets: "{}"
        backend_class: "SortedSet"
```

### Implementation

The backend class must implement `static fn from(items: [T]) -> Self`:

```simple
class SortedSet<T>:
    items: [T]

impl SortedSet:
    static fn from(items: [T]) -> SortedSet<T>:
        """Create sorted set from array."""
        val sorted_items = items.sorted()
        SortedSet(items: sorted_items)

    fn to_list() -> [T]:
        self.items
```

### Usage

```simple
val sorted = sorted{3, 1, 2}  # Creates SortedSet([1, 2, 3])
check sorted.to_list() == [1, 2, 3]
```

## Comparison with Constructor Syntax

**Before (no set literals):**

```simple
val nums = Set.new()
nums.insert(1)
nums.insert(2)
nums.insert(3)
```

**After (with set literals):**

```simple
val nums = s{1, 2, 3}
```

Both are equivalent, but literals are more concise and readable.

## Technical Details

### Syntax

Set literals use the syntax:

```
set_literal = prefix "{" [elements] "}"
elements    = expr ("," expr)* [","]
prefix      = "s" | custom_prefix
```

- The prefix is configurable via `simple.sdn`
- Trailing commas are allowed
- Empty sets require type annotation

### Compilation

Set literals are lowered during compilation:

```simple
# Source
val nums = s{1, 2, 3}

# Lowered to (conceptually)
val nums = Set.new()
nums.insert(1)
nums.insert(2)
nums.insert(3)
```

### Type System

- Type: `Set<T>` where `T` is the element type
- Type inference: element type inferred from first element
- Empty sets: require type annotation (`Set<T>`)

## Best Practices

1. **Use literals for readability:**
   ```simple
   # Good
   val nums = s{1, 2, 3}

   # Verbose
   val nums = Set.new()
   nums.insert(1)
   nums.insert(2)
   nums.insert(3)
   ```

2. **Type annotation for empty sets:**
   ```simple
   # Good
   val empty: Set<i64> = s{}

   # Error - type cannot be inferred
   val empty = s{}
   ```

3. **Prefer set literals over list-to-set conversion:**
   ```simple
   # Good
   val nums = s{1, 2, 3}

   # Acceptable but verbose
   val nums = Set.from([1, 2, 3])
   ```

## See Also

- [Set API Documentation](../api/set.md)
- [Collection Types](../guide/collections.md)
- [Configuration Guide](../guide/configuration.md)
