# Collection Utilities Specification

**Feature ID:** #COLL-UTIL-001 to #COLL-UTIL-052 | **Category:** Runtime | Collections | **Status:** Implemented

_Source: `test/feature/usage/collection_utilities_spec.spl`_

---

## Array Utility Methods

```simple
# Sorting (returns new array)
val sorted = arr.sort()      # Returns new sorted array
val sorted = arr.sorted()    # Alias for sort

# Reversing (returns new array)
val rev = arr.reverse()      # Returns new reversed array
val rev = arr.reversed()     # Alias for reverse

# Access
arr.first()             # First element or nil
arr.last()              # Last element or nil
arr.index_of(value)     # Index or -1 if not found

# Aggregation
arr.sum()               # Sum of numeric elements
arr.min()               # Minimum value or nil
arr.max()               # Maximum value or nil
arr.count_of(value)     # Count occurrences of specific value

# Transformation
arr.concat(other)       # Concatenate arrays
arr.copy()              # Shallow copy
arr.zip(other)          # Zip into tuples
arr.enumerate()         # Add indices as tuples
arr.flatten()           # Flatten nested arrays
arr.unique()            # Remove duplicates
arr.take(n)             # First n elements
arr.drop(n)             # Skip first n elements

# Predicates
arr.all_truthy()        # All elements truthy?
arr.any_truthy()        # Any element truthy?
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 40 |

## Test Structure

### Array Sorting

- ✅ sort returns new sorted array
- ✅ sorted returns new sorted array
### Array Reversing

- ✅ reverse returns new reversed array
- ✅ reversed returns new reversed array
### Array Access Methods

- ✅ first returns first element
- ✅ last returns last element
- ✅ first returns nil for empty array
- ✅ last returns nil for empty array
- ✅ index_of finds element
- ✅ index_of returns -1 when not found
### Array Concatenation and Copy

- ✅ concatenates two arrays
- ✅ creates shallow copy
### Array Aggregation

- ✅ sums numeric array
- ✅ sum of empty array is zero
- ✅ finds minimum value
- ✅ finds maximum value
- ✅ min of empty array is nil
- ✅ max of empty array is nil
- ✅ counts occurrences
### Array Transformation

- ✅ zips two arrays into tuples
- ✅ enumerates array with indices
- ✅ flattens nested arrays
- ✅ removes duplicates
### Array Slicing Methods

- ✅ takes first n elements
- ✅ drops first n elements
### Array Predicates

- ✅ all_truthy returns true when all truthy
- ✅ all_truthy returns false with zero
- ✅ any_truthy returns true with some truthy
- ✅ any_truthy returns false when all zero
### Array Fill

- ✅ fills array with value
### Tuple Operations

- ✅ creates tuple with specified size
- ✅ gets tuple elements by index
- ✅ first and last on tuple
### String Operations

- ✅ creates string and gets length
- ✅ concatenates strings
- ✅ handles empty string
### Dictionary Operations

- ✅ creates empty dict
- ✅ sets and gets values
- ✅ overwrites existing key
- ✅ returns nil for missing key

