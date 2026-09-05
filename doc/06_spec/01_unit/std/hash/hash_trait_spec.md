# Hash Trait Specification

> Tests covering Hash trait, Text hashing, Integer hashing, Boolean hashing, Collection hashing, Pair hashing, Hash characteristics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hash Trait Specification

## Scenarios

### Hash trait

### Text hashing

#### is stable for the same string

- is stable for the same string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is stable for the same string")
val h1 = hash_text("hello")
val h2 = hash_text("hello")
check(h1 == h2)
```

</details>

#### changes for different strings

- changes for different strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes for different strings")
check(hash_text("hello") != hash_text("world"))
```

</details>

#### handles empty string

- handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
check(hash_text("") == 17)
```

</details>

#### treats unicode input as distinct

- treats unicode input as distinct


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats unicode input as distinct")
check(hash_text("hello") != hash_text("héllo"))
```

</details>

### Integer hashing

#### is stable for the same integer

- is stable for the same integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is stable for the same integer")
check(hash_int(42) == hash_int(42))
```

</details>

#### changes across adjacent integers

- changes across adjacent integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes across adjacent integers")
check(hash_int(42) != hash_int(43))
```

</details>

#### handles negative values

- handles negative values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles negative values")
check(hash_int(-1) != hash_int(0))
```

</details>

### Boolean hashing

#### maps true and false to different hashes

- maps true and false to different hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps true and false to different hashes")
check(hash_bool(true) != hash_bool(false))
```

</details>

#### maps false to zero

- maps false to zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps false to zero")
check(hash_bool(false) == 0)
```

</details>

### Collection hashing

#### combines array element hashes

- combines array element hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines array element hashes")
val a = hash_array([1, 2, 3])
val b = hash_array([1, 2, 4])
check(a != b)
```

</details>

#### is order sensitive

- is order sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is order sensitive")
check(hash_array([1, 2, 3]) != hash_array([3, 2, 1]))
```

</details>

#### preserves uniqueness across a small sample

- preserves uniqueness across a small sample


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves uniqueness across a small sample")
val hashes = [
    hash_text("a"),
    hash_text("hi"),
    hash_text("at"),
    hash_text("ah"),
    hash_text("fly"),
    hash_text("bit"),
    hash_text("stop"),
    hash_text("zebra")
]
check(unique_count(hashes) == hashes.len())
```

</details>

### Pair hashing

#### combines tuple-like values

- combines tuple-like values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines tuple-like values")
check(hash_pair(42, 7) != hash_pair(42, 8))
```

</details>

#### is order sensitive

- is order sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is order sensitive")
check(hash_pair(1, 2) != hash_pair(2, 1))
```

</details>

### Hash characteristics

#### changes when one character changes

- changes when one character changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes when one character changes")
val h1 = hash_text("test")
val h2 = hash_text("tesa")
check(h1 != h2)
```

</details>

#### remains non-zero for non-empty input

- remains non-zero for non-empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remains non-zero for non-empty input")
check(hash_text("sample") != 0)
```

</details>

#### keeps repeated hashing consistent

- keeps repeated hashing consistent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps repeated hashing consistent")
val first = hash_array([hash_int(1), hash_int(2), hash_int(3)])
val second = hash_array([hash_int(1), hash_int(2), hash_int(3)])
check(first == second)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/hash/hash_trait_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hash trait, Text hashing, Integer hashing, Boolean hashing, Collection hashing, Pair hashing, Hash characteristics.
- Hash trait
- Text hashing
- Integer hashing
- Boolean hashing
- Collection hashing
- Pair hashing
- Hash characteristics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a5d7d045b3832d9058feac5b34cae0320899b0206011e749177f5775f82f28db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5d7d045b3832d9058feac5b34cae0320899b0206011e749177f5775f82f28db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5d7d045b3832d9058feac5b34cae0320899b0206011e749177f5775f82f28db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/hash/hash_trait_spec.spl
mirror: doc/06_spec/01_unit/std/hash/hash_trait_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/hash/hash_trait_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/hash/hash_trait_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/hash/hash_trait_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is stable for the same string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/hash/hash_trait_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'changes for different strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/hash/hash_trait_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
