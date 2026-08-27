# Advanced Indexing and Slicing Specification

> Tests for advanced indexing features including:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Indexing and Slicing Specification

Tests for advanced indexing features including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1015, #1016, #1017 |
| Category | Language, Collections |
| Status | Complete |
| Source | `test/03_system/feature/usage/advanced_indexing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for advanced indexing features including:
- Negative indexing (Python-style -1, -2, etc.)
- Slice operations with start:end:step syntax
- String slicing
- Multi-dimensional indexing

## Scenarios

### Advanced Indexing

#### negative indexing

#### accesses last element with -1

- accesses last element with -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses last element with -1")
val arr = [10, 20, 30, 40, 50]
expect arr[-1] == 50
```

</details>

#### accesses second-to-last with -2

- accesses second-to-last with -2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses second-to-last with -2")
val arr = [10, 20, 30, 40, 50]
expect arr[-2] == 40
```

</details>

#### accesses first element with negative index

- accesses first element with negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses first element with negative index")
val arr = [10, 20, 30]
expect arr[-3] == 10
```

</details>

#### works with strings

- works with strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with strings")
val s = "Hello"
expect s[-1] == "o"
expect s[-5] == "H"
```

</details>

#### negative indexing with single element

- negative indexing with single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("negative indexing with single element")
val arr = [42]
expect arr[-1] == 42
```

</details>

#### slicing operations

#### slices with start and end

- slices with start and end


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with start and end")
val arr = [10, 20, 30, 40, 50]
expect arr[1:4] == [20, 30, 40]
```

</details>

#### slices from beginning

- slices from beginning


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices from beginning")
val arr = [10, 20, 30, 40, 50]
expect arr[:3] == [10, 20, 30]
```

</details>

#### slices to end

- slices to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices to end")
val arr = [10, 20, 30, 40, 50]
expect arr[2:] == [30, 40, 50]
```

</details>

#### slices with step

- slices with step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with step")
val arr = [10, 20, 30, 40, 50]
expect arr[::2] == [10, 30, 50]
```

</details>

#### reverses via .reversed(), not a negative-step slice

- reverses via .reversed(), not a negative-step slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses via .reversed(), not a negative-step slice")
# Negative slice STEP is not part of the language -- see
# doc/04_architecture/language/slicing/+adr/
# negative_step_not_supported_2026-07-30.md and
# test/03_system/feature/usage/negative_step_slice_spec.spl.
val arr = [10, 20, 30, 40, 50]
expect arr.reversed() == [50, 40, 30, 20, 10]
```

</details>

#### slices with start:end:step

- slices with start:end:step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with start:end:step")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[2:8:2] == [2, 4, 6]
```

</details>

#### empty slice

- empty slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("empty slice")
val arr = [10, 20, 30]
expect arr[5:10] == []
```

</details>

#### string slicing

#### slices substring

- slices substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices substring")
val s = "Hello World"
expect s[0:5] == "Hello"
```

</details>

#### slices from end

- slices from end


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices from end")
val s = "Hello World"
expect s[-5:] == "World"
```

</details>

#### slices middle

- slices middle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices middle")
val s = "abcdefgh"
expect s[2:6] == "cdef"
```

</details>

#### reverses string via .reversed(), not a negative-step slice

- reverses string via .reversed(), not a negative-step slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses string via .reversed(), not a negative-step slice")
val s = "Hello"
expect s.reversed() == "olleH"
```

</details>

#### handles UTF-8 characters

- handles UTF-8 characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles UTF-8 characters")
val s = "Hello 🌍 World"
expect s[6:7] == "🌍"
```

</details>

#### combined operations

#### slices with negative start

- slices with negative start


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with negative start")
val arr = [10, 20, 30, 40, 50]
expect arr[-3:] == [30, 40, 50]
```

</details>

#### slices with negative end

- slices with negative end


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with negative end")
val arr = [10, 20, 30, 40, 50]
expect arr[:-2] == [10, 20, 30]
```

</details>

#### slices with both negative

- slices with both negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with both negative")
val arr = [10, 20, 30, 40, 50]
expect arr[-4:-1] == [20, 30, 40]
```

</details>

#### negative indices in string slice

- negative indices in string slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("negative indices in string slice")
val s = "Hello World"
expect s[-5:-1] == "Worl"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `7239f198c27693c6b40c37b9439857c511ffecadf595d203576ab68b2939472e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7239f198c27693c6b40c37b9439857c511ffecadf595d203576ab68b2939472e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7239f198c27693c6b40c37b9439857c511ffecadf595d203576ab68b2939472e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/advanced_indexing_spec.spl
mirror: doc/06_spec/03_system/feature/usage/advanced_indexing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/advanced_indexing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/advanced_indexing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/advanced_indexing_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accesses last element with -1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/advanced_indexing_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accesses second-to-last with -2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/advanced_indexing_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accesses first element with negative index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
