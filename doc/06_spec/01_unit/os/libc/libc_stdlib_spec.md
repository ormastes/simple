# libc_stdlib_spec

> Verifies the libc stdlib behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# libc_stdlib_spec

Verifies the libc stdlib behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_stdlib_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the libc stdlib behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS libc stdlib (musl-shaped)

### libc_atol

#### parses simple decimal

- Verify: parses simple decimal
   - Expected: libc_atol("42".bytes()) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: parses simple decimal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("42".bytes())).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses negative

- Verify: parses negative
   - Expected: libc_atol("-42".bytes()) equals `-42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: parses negative")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("-42".bytes())).to_equal(-42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### parses positive sign

- Verify: parses positive sign
   - Expected: libc_atol("+42".bytes()) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: parses positive sign")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("+42".bytes())).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### skips leading whitespace

- Verify: skips leading whitespace
   - Expected: libc_atol("  42".bytes()) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: skips leading whitespace")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("  42".bytes())).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### stops at non-digit

- Verify: stops at non-digit
   - Expected: libc_atol("42abc".bytes()) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: stops at non-digit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("42abc".bytes())).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### stops at non-digit after sign

- Verify: stops at non-digit after sign
   - Expected: libc_atol("-42x".bytes()) equals `-42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: stops at non-digit after sign")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("-42x".bytes())).to_equal(-42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles zero

- Verify: handles zero
   - Expected: libc_atol("0".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles zero")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("0".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles large number

- Verify: handles large number
   - Expected: libc_atol("1234567".bytes()) equals `1234567)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles large number")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("1234567".bytes())).to_equal(1234567)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty or non-numeric

- Verify: handles empty or non-numeric
   - Expected: libc_atol("abc".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles empty or non-numeric")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_atol("abc".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_abs

#### returns positive unchanged

- Verify: returns positive unchanged
   - Expected: libc_abs(42) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns positive unchanged")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_abs(42)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns negative as positive

- Verify: returns negative as positive
   - Expected: libc_abs(-42) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns negative as positive")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_abs(-42)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles zero

- Verify: handles zero
   - Expected: libc_abs(0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles zero")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_abs(0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_labs

#### returns positive unchanged

- Verify: returns positive unchanged
   - Expected: libc_labs(42) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns positive unchanged")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_labs(42)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns negative as positive

- Verify: returns negative as positive
   - Expected: libc_labs(-42) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns negative as positive")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_labs(-42)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles zero

- Verify: handles zero
   - Expected: libc_labs(0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles zero")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_labs(0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_max

#### returns greater value

- Verify: returns greater value
   - Expected: libc_max(10, 20) equals `20)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns greater value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_max(10, 20)).to_equal(20)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns greater when first is larger

- Verify: returns greater when first is larger
   - Expected: libc_max(30, 10) equals `30)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns greater when first is larger")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_max(30, 10)).to_equal(30)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles equal values

- Verify: handles equal values
   - Expected: libc_max(42, 42) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles equal values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_max(42, 42)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles negatives

- Verify: handles negatives
   - Expected: libc_max(-10, -5) equals `-5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles negatives")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_max(-10, -5)).to_equal(-5)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_min

#### returns lesser value

- Verify: returns lesser value
   - Expected: libc_min(10, 20) equals `10)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns lesser value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_min(10, 20)).to_equal(10)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns lesser when second is smaller

- Verify: returns lesser when second is smaller
   - Expected: libc_min(30, 10) equals `10)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns lesser when second is smaller")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_min(30, 10)).to_equal(10)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles equal values

- Verify: handles equal values
   - Expected: libc_min(42, 42) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles equal values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_min(42, 42)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles negatives

- Verify: handles negatives
   - Expected: libc_min(-10, -5) equals `-10)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles negatives")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(libc_min(-10, -5)).to_equal(-10)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_bsearch

#### finds element at beginning

- Verify: finds element at beginning
   - Expected: libc_bsearch(arr, 1) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: finds element at beginning")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [1, 2, 3, 4, 5]
expect(libc_bsearch(arr, 1)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### finds element in middle

- Verify: finds element in middle
   - Expected: libc_bsearch(arr, 3) equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: finds element in middle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [1, 2, 3, 4, 5]
expect(libc_bsearch(arr, 3)).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### finds element at end

- Verify: finds element at end
   - Expected: libc_bsearch(arr, 5) equals `4)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: finds element at end")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [1, 2, 3, 4, 5]
expect(libc_bsearch(arr, 5)).to_equal(4)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when not found

- Verify: returns -1 when not found
   - Expected: libc_bsearch(arr, 10) equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns -1 when not found")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [1, 2, 3, 4, 5]
expect(libc_bsearch(arr, 10)).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 for empty array

- Verify: returns -1 for empty array
   - Expected: libc_bsearch(arr, 5) equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: returns -1 for empty array")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr: [i64] = []
expect(libc_bsearch(arr, 5)).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### finds in single element array

- Verify: finds in single element array
   - Expected: libc_bsearch(arr, 42) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: finds in single element array")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [42]
expect(libc_bsearch(arr, 42)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles negative numbers

- Verify: handles negative numbers
   - Expected: libc_bsearch(arr, -2) equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles negative numbers")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [-5, -2, 0, 3, 7]
expect(libc_bsearch(arr, -2)).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

### libc_qsort

#### sorts unsorted array

- Verify: sorts unsorted array
   - Expected: sorted.len() equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[0] equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[1] equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[2] equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[3] equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[4] equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: sorts unsorted array")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [3, 1, 4, 1, 5]
val sorted = libc_qsort(arr)
expect(sorted.len()).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(sorted[0]).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(sorted[1]).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(sorted[2]).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(sorted[3]).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(sorted[4]).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles array with negatives

- Verify: handles array with negatives
   - Expected: sorted[0] equals `-5)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[1] equals `-1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[2] equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[3] equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[4] equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles array with negatives")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [3, -1, 0, -5, 2]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(-5)  # oracle: pinned constant asserted by this scenario
expect(sorted[1]).to_equal(-1)  # oracle: pinned constant asserted by this scenario
expect(sorted[2]).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(sorted[3]).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sorted[4]).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles array with duplicates

- Verify: handles array with duplicates
   - Expected: sorted[0] equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[1] equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[2] equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[3] equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[4] equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles array with duplicates")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [5, 2, 5, 1, 2]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(sorted[1]).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sorted[2]).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sorted[3]).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(sorted[4]).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

#### leaves original array unchanged

- Verify: leaves original array unchanged
   - Expected: arr[0] equals `orig_first`
   - Expected: arr[0] equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: leaves original array unchanged")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [3, 1, 4, 1, 5]
val orig_first = arr[0]
val sorted = libc_qsort(arr)
expect(arr[0]).to_equal(orig_first)
expect(arr[0]).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles already sorted array

- Verify: handles already sorted array
   - Expected: sorted[0] equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[4] equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles already sorted array")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [1, 2, 3, 4, 5]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(sorted[4]).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles reverse sorted array

- Verify: handles reverse sorted array
   - Expected: sorted[0] equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[4] equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles reverse sorted array")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [5, 4, 3, 2, 1]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(sorted[4]).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles single element

- Verify: handles single element
   - Expected: sorted[0] equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles single element")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr = [42]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty array

- Verify: handles empty array
   - Expected: sorted.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDLIB-001
step("Verify: handles empty array")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val arr: [i64] = []
val sorted = libc_qsort(arr)
expect(sorted.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f980514a3e593a8e7039e9252d2015f99d4e82d382c1c77df2a283b822d5bdcf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f980514a3e593a8e7039e9252d2015f99d4e82d382c1c77df2a283b822d5bdcf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f980514a3e593a8e7039e9252d2015f99d4e82d382c1c77df2a283b822d5bdcf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/libc/libc_stdlib_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_stdlib_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/libc/libc_stdlib_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/libc/libc_stdlib_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_stdlib_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
