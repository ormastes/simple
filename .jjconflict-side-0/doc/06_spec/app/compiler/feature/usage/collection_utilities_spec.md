# Collection Utilities Specification

Tests collection utility functions including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLL-UTIL-001 to #COLL-UTIL-052 |
| Category | Runtime \| Collections |
| Status | Implemented |
| Source | `test/feature/usage/collection_utilities_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests collection utility functions including:
- Array sorting and reversing
- Array aggregation (sum, min, max, count)
- Array transformation (zip, enumerate, flatten, unique)
- Array slicing (take, drop)
- Array predicates (all_truthy, any_truthy)
- Tuple operations
- String operations
- Dictionary operations

## Array Utility Methods

```simple
val sorted = arr.sort()      # Returns new sorted array
val sorted = arr.sorted()    # Alias for sort

val rev = arr.reverse()      # Returns new reversed array
val rev = arr.reversed()     # Alias for reverse

arr.first()             # First element or nil
arr.last()              # Last element or nil
arr.index_of(value)     # Index or -1 if not found

arr.sum()               # Sum of numeric elements
arr.min()               # Minimum value or nil
arr.max()               # Maximum value or nil
arr.count_of(value)     # Count occurrences of specific value

arr.concat(other)       # Concatenate arrays
arr.copy()              # Shallow copy
arr.zip(other)          # Zip into tuples
arr.enumerate()         # Add indices as tuples
arr.flatten()           # Flatten nested arrays
arr.unique()            # Remove duplicates
arr.take(n)             # First n elements
arr.drop(n)             # Skip first n elements

arr.all_truthy()        # All elements truthy?
arr.any_truthy()        # Any element truthy?
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/collection_utilities/result.json` |

## Scenarios

- sort returns new sorted array
- sorted returns new sorted array
- reverse returns new reversed array
- reversed returns new reversed array
- first returns first element
- last returns last element
- first returns nil for empty array
- last returns nil for empty array
- index_of finds element
- index_of returns -1 when not found
- concatenates two arrays
- creates shallow copy
- sums numeric array
- sum of empty array is zero
- finds minimum value
- finds maximum value
- min of empty array is nil
- max of empty array is nil
- counts occurrences
- zips two arrays into tuples
- enumerates array with indices
- flattens nested arrays
- removes duplicates
- takes first n elements
- drops first n elements
- all_truthy returns true when all truthy
- all_truthy returns false with zero
- any_truthy returns true with some truthy
- any_truthy returns false when all zero
- fills array with value
- creates tuple with specified size
- gets tuple elements by index
- first and last on tuple
- creates string and gets length
- concatenates strings
- handles empty string
- creates empty dict
- sets and gets values
- overwrites existing key
- returns nil for missing key
