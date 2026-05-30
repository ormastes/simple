# Range Step Specification

**Feature ID:** #RANGE-STEP | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/range_step_by_spec.spl`_

---

## Syntax

```simple
# Slice with step
arr[::2]       # Every other element (step=2)
arr[1::2]      # Every other starting from index 1
arr[::-1]      # Reversed
arr[1:5:2]     # Slice from 1 to 5 with step 2

# Range iteration (stdlib method)
for i in (0..10).step_by(2):
    print i    # 0, 2, 4, 6, 8
```

## Key Behaviors

- Step value can be positive (forward) or negative (reverse)
- Step of 1 is the default (every element)
- Step of -1 reverses the sequence
- Step of 2 selects every other element
- Works on arrays, strings, and any sliceable type

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 25 |

## Test Structure

### Range Step (Slicing with Step)

#### basic step on arrays

- ✅ selects every other element with step 2
- ✅ selects every third element with step 3
- ✅ selects every fourth element
#### step with start offset

- ✅ starts from index 1 with step 2
- ✅ starts from index 2 with step 3
- ✅ starts from middle of array
#### step with start and end

- ✅ slices range with step
- ✅ slices narrow range with step
- ✅ slices with step larger than range
#### negative step (reverse)

- ✅ reverses entire array
- ✅ reverses empty array
- ✅ reverses single element
- ✅ reverses with step -2
#### step on strings

- ✅ selects every other character
- ✅ reverses string
- ✅ selects odd-indexed characters
- ✅ slices string with step
#### edge cases

- ✅ handles step equal to length
- ✅ handles step greater than length
- ✅ handles step of 1 (identity)
- ✅ handles empty slice with step
#### practical examples

- ✅ extracts even indices
- ✅ extracts odd indices
- ✅ reverses for iteration
- ✅ samples at regular intervals

