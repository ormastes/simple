# List<Option<T>>::compact() - Remove None Values

The `compact()` method is available on lists of optional values (`List<Option<T>>`) and removes all `None` values while unwrapping `Some` values.

## Syntax

```simple
val result: List<T> = list_of_options.compact()
```

## Overview

- **Input**: `List<Option<T>>`
- **Output**: `List<T>` 
- **Operation**: Filters out `None` values and unwraps `Some` values
- **Inspiration**: Ruby's `Array#compact` method

## Examples

### Basic Usage

```simple
val items: List<Option<i64>> = [Some(1), None, Some(2), None, Some(3)]
val compacted = items.compact()
# Result: [1, 2, 3]
```

### Empty and Edge Cases

```simple
# Empty list
val empty: List<Option<i64>> = []
empty.compact()  # => []

# All None values
val all_none: List<Option<i64>> = [None, None, None]
all_none.compact()  # => []

# All Some values
val all_some: List<Option<i64>> = [Some(1), Some(2), Some(3)]
all_some.compact()  # => [1, 2, 3]
```

### Chaining with map()

```simple
val numbers = [1, 2, 3, 4, 5]

# Map to Option (filter evens), then compact
val evens = numbers
    .map(fn(x): 
        if x % 2 == 0:
            Some(x * 10)
        else:
            None
    )
    .compact()
# Result: [20, 40]
```

### Working with Text

```simple
val words: List<Option<text>> = [
    Some("hello"),
    None,
    Some("world"),
    None
]
val compacted = words.compact()
# Result: ["hello", "world"]
```

### Nested Structures

```simple
val items: List<Option<List<i64>>> = [
    Some([1, 2]),
    None,
    Some([3, 4]),
    None,
    Some([5])
]
val compacted = items.compact()
# Result: [[1, 2], [3, 4], [5]]
```

## Implementation Details

The `compact()` method:

1. Creates a new empty list of type `List<T>`
2. Iterates through each element in the original list
3. For each `Some(value)`, pushes the unwrapped value to the result list
4. For each `None`, skips the element
5. Returns the new list

The original list is not modified (immutable operation).

## Performance Characteristics

- **Time Complexity**: O(n) where n is the length of the original list
- **Space Complexity**: O(k) where k is the number of `Some` values
- **Allocation**: Creates a new list; does not modify the original

## Comparison with Other Languages

### Ruby

```ruby
[1, nil, 2, nil, 3].compact
# => [1, 2, 3]
```

### Simple

```simple
[Some(1), None, Some(2), None, Some(3)].compact()
# => [1, 2, 3]
```

The key difference is that Ruby uses `nil` for absent values while Simple uses the type-safe `Option<T>` with explicit `Some` and `None` variants.

## Type System Notes

### Specialized Implementation

The `compact()` method is implemented in a specialized `impl<T> List<Option<T>>` block:

```simple
impl<T> List<Option<T>>:
    fn compact() -> List<T>:
        # Implementation...
```

This means `compact()` is only available on lists where the element type is `Option<T>`. It won't appear on regular `List<i64>` or `List<text>`.

### Future: Type Equality Constraints

An alternative implementation using type equality constraints would look like:

```simple
impl List<T>:
    fn compact<U>() -> List<U> where T = Option<U>:
        # This syntax is not yet supported
```

This would allow `compact()` to be defined alongside other List methods with a constraint that `T` must be `Option<U>`. Simple currently uses specialized impl blocks instead.

## Common Patterns

### Filter-Map Pattern

```simple
# Transform and filter in one pass
val results = values
    .map(fn(x): try_parse(x))  # Returns Option<T>
    .compact()                  # Removes failures

# Equivalent to Rust's filter_map
```

### Error Handling

```simple
fn safe_divide(a: i64, b: i64) -> Option<i64>:
    if b == 0:
        None
    else:
        Some(a / b)

val denominators = [1, 0, 2, 0, 4]
val results = denominators
    .map(fn(d): safe_divide(10, d))
    .compact()
# Result: [10, 5, 2]  (skipped division by zero)
```

## Related Methods

- `filter()` - Remove elements based on predicate
- `filter_map()` - Transform and filter in one operation (future)
- `flatten()` - Flatten nested lists
- `map()` - Transform each element

## See Also

- [Option<T> Type Guide](option_type.md)
- [List Methods Reference](list_methods.md)
- [Functional Programming Patterns](functional_patterns.md)
