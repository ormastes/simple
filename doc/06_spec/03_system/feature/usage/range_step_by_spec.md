# Range Step Specification

> arr[::2]       # Every other element (step=2)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Range Step Specification

arr[::2]       # Every other element (step=2)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RANGE-STEP |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/range_step_by_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Slice with step (step must be positive)
arr[::2]       # Every other element (step=2)
arr[1::2]      # Every other starting from index 1
arr[1:5:2]     # Slice from 1 to 5 with step 2
arr.reversed() # Reverse -- NOT arr[::-1] (errors)

# Range iteration (stdlib method)
for i in (0..10).step_by(2):
print i    # 0, 2, 4, 6, 8
```

## Key Behaviors

- Step value must be positive; negative step is a hard error (see the ADR)
- Step of 1 is the default (every element)
- Step of 2 selects every other element
- Works on arrays, strings, and any sliceable type
- To reverse a sequence, call `.reversed()` explicitly

## Scenarios

### Range Step (Slicing with Step)

#### basic step on arrays

#### selects every other element with step 2

- selects every other element with step 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects every other element with step 2")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[::2] == [0, 2, 4, 6, 8]
```

</details>

#### selects every third element with step 3

- selects every third element with step 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects every third element with step 3")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[::3] == [0, 3, 6, 9]
```

</details>

#### selects every fourth element

- selects every fourth element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects every fourth element")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
expect arr[::4] == [0, 4, 8]
```

</details>

#### step with start offset

#### starts from index 1 with step 2

- starts from index 1 with step 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts from index 1 with step 2")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[1::2] == [1, 3, 5, 7, 9]
```

</details>

#### starts from index 2 with step 3

- starts from index 2 with step 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts from index 2 with step 3")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[2::3] == [2, 5, 8]
```

</details>

#### starts from middle of array

- starts from middle of array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts from middle of array")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[5::2] == [5, 7, 9]
```

</details>

#### step with start and end

#### slices range with step

- slices range with step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices range with step")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[1:8:2] == [1, 3, 5, 7]
```

</details>

#### slices narrow range with step

- slices narrow range with step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices narrow range with step")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[2:6:2] == [2, 4]
```

</details>

#### slices with step larger than range

- slices with step larger than range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with step larger than range")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[0:5:10] == [0]
```

</details>

#### reversal is .reversed(), not negative step

#### reverses entire array via .reversed()

- reverses entire array via .reversed()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses entire array via .reversed()")
val arr = [1, 2, 3, 4, 5]
expect arr.reversed() == [5, 4, 3, 2, 1]
```

</details>

#### reverses empty array via .reversed()

- reverses empty array via .reversed()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses empty array via .reversed()")
val arr: [i64] = []
expect arr.reversed() == []
```

</details>

#### reverses single element via .reversed()

- reverses single element via .reversed()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses single element via .reversed()")
val arr = [42]
expect arr.reversed() == [42]
```

</details>

#### step on strings

#### selects every other character

- selects every other character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects every other character")
val s = "abcdefgh"
expect s[::2] == "aceg"
```

</details>

#### reverses string via .reversed()

- reverses string via .reversed()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses string via .reversed()")
val s = "hello"
expect s.reversed() == "olleh"
```

</details>

#### selects odd-indexed characters

- selects odd-indexed characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects odd-indexed characters")
val s = "abcdefgh"
expect s[1::2] == "bdfh"
```

</details>

#### slices string with step

- slices string with step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices string with step")
val s = "0123456789"
expect s[1:8:2] == "1357"
```

</details>

#### edge cases

#### handles step equal to length

- handles step equal to length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles step equal to length")
val arr = [1, 2, 3, 4, 5]
expect arr[::5] == [1]
```

</details>

#### handles step greater than length

- handles step greater than length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles step greater than length")
val arr = [1, 2, 3, 4, 5]
expect arr[::10] == [1]
```

</details>

#### handles step of 1 (identity)

- handles step of 1 (identity)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles step of 1 (identity)")
val arr = [1, 2, 3, 4, 5]
expect arr[::1] == [1, 2, 3, 4, 5]
```

</details>

#### handles empty slice with step

- handles empty slice with step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty slice with step")
val arr = [1, 2, 3, 4, 5]
expect arr[5:5:2] == []
```

</details>

#### practical examples

#### extracts even indices

- extracts even indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts even indices")
val data = ["a", "b", "c", "d", "e", "f"]
expect data[::2] == ["a", "c", "e"]
```

</details>

#### extracts odd indices

- extracts odd indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts odd indices")
val data = ["a", "b", "c", "d", "e", "f"]
expect data[1::2] == ["b", "d", "f"]
```

</details>

#### reverses for iteration via .reversed()

- reverses for iteration via .reversed()


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses for iteration via .reversed()")
val nums = [1, 2, 3, 4, 5]
var sum = 0
for n in nums.reversed():
    sum = sum * 10 + n
expect sum == 54321
```

</details>

#### samples at regular intervals

- samples at regular intervals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("samples at regular intervals")
val readings = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
val sampled = readings[::3]
expect sampled == [10, 40, 70, 100]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `86711a9764b9f0b4f54db6511f841e4fa9b7a6138b9b37f96d089edee317ae28`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86711a9764b9f0b4f54db6511f841e4fa9b7a6138b9b37f96d089edee317ae28`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86711a9764b9f0b4f54db6511f841e4fa9b7a6138b9b37f96d089edee317ae28`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/range_step_by_spec.spl
mirror: doc/06_spec/03_system/feature/usage/range_step_by_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/range_step_by_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/range_step_by_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/range_step_by_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects every other element with step 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/range_step_by_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects every third element with step 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/range_step_by_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects every fourth element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
