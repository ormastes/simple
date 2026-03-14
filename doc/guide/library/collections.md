# Collections

This chapter covers Simple's built-in collection types, their APIs, and common usage patterns.

## List

Ordered, growable sequence of elements.

```simple
val items = [1, 2, 3]
var mutable_list = [1, 2, 3]

# Access
items[0]                    # 1
items.len()                 # 3
items.is_empty()            # false

# Mutation (requires var)
mutable_list.push(4)
mutable_list.pop()
mutable_list.insert(0, 99)
mutable_list.remove(1)

# Iteration
for item in items:
    print item

# Functional
items.map(_ * 2)
items.filter(_ > 1)
items.reduce(0, _1 + _2)
```

## Dict

Key-value mapping (hash map).

```simple
val ages = {"alice": 30, "bob": 25}

# Access
ages["alice"]               # 30
ages.get("carol")           # nil

# Mutation (requires var)
var d = {}
d["key"] = "value"
d.remove("key")

# Iteration
for (key, value) in ages:
    print "{key}: {value}"

# Query
ages.keys()
ages.values()
ages.contains_key("alice")  # true
ages.len()                  # 2
```

## Set

Unordered collection of unique elements.

```simple
val s = Set([1, 2, 3])

s.contains(2)              # true
s.len()                    # 3

# Set operations
val a = Set([1, 2, 3])
val b = Set([2, 3, 4])
a.union(b)                 # {1, 2, 3, 4}
a.intersection(b)          # {2, 3}
a.difference(b)            # {1}
```

## Array (Fixed-Size)

Fixed-length array with compile-time known size.

```simple
val arr: Array<Int, 4> = [1, 2, 3, 4]
arr[0]                      # 1
arr.len()                   # 4 (compile-time constant)
```

## Ranges

```simple
0..10                       # 0 to 9 (exclusive end)
0..=10                      # 0 to 10 (inclusive end)

for i in 0..5:
    print i

val slice = items[1..3]     # Sublist from index 1 to 2
```

## Common Patterns

### Chained Operations

Use intermediate `var` for chained methods (chained methods limitation):

```simple
# Instead of: items.filter(_ > 0).map(_ * 2).take(5)
var filtered = items.filter(_ > 0)
var mapped = filtered.map(_ * 2)
val result = mapped.take(5)
```

### Comprehensions

```simple
val squares = [for x in 0..10: x * x]
val evens = [for x in items if x % 2 == 0: x]
```

## See Also

- [Standard Library Overview](stdlib.md) for the full standard library
- [Closures & Functional Patterns](../language/closures.md) for iterator methods
- [Type System](../language/type_system.md) for generic collection types
