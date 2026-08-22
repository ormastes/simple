# hash_trait_spec

> Verifies the hash trait behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hash_trait_spec

Verifies the hash trait behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/hash/hash_trait_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the hash trait behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Hash trait

### Text hashing

#### is stable for the same string

- Verify: is stable for the same string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: is stable for the same string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val h1 = hash_text("hello")
val h2 = hash_text("hello")
check(h1 == h2)
```

</details>

#### changes for different strings

- Verify: changes for different strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: changes for different strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_text("hello") != hash_text("world"))
```

</details>

#### handles empty string

- Verify: handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: handles empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_text("") == 17)
```

</details>

#### treats unicode input as distinct

- Verify: treats unicode input as distinct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: treats unicode input as distinct")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_text("hello") != hash_text("héllo"))
```

</details>

### Integer hashing

#### is stable for the same integer

- Verify: is stable for the same integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: is stable for the same integer")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_int(42) == hash_int(42))
```

</details>

#### changes across adjacent integers

- Verify: changes across adjacent integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: changes across adjacent integers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_int(42) != hash_int(43))
```

</details>

#### handles negative values

- Verify: handles negative values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: handles negative values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_int(-1) != hash_int(0))
```

</details>

### Boolean hashing

#### maps true and false to different hashes

- Verify: maps true and false to different hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: maps true and false to different hashes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_bool(true) != hash_bool(false))
```

</details>

#### maps false to zero

- Verify: maps false to zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: maps false to zero")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_bool(false) == 0)
```

</details>

### Collection hashing

#### combines array element hashes

- Verify: combines array element hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: combines array element hashes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = hash_array([1, 2, 3])
val b = hash_array([1, 2, 4])
check(a != b)
```

</details>

#### is order sensitive

- Verify: is order sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: is order sensitive")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_array([1, 2, 3]) != hash_array([3, 2, 1]))
```

</details>

#### preserves uniqueness across a small sample

- Verify: preserves uniqueness across a small sample


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: preserves uniqueness across a small sample")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: combines tuple-like values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: combines tuple-like values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_pair(42, 7) != hash_pair(42, 8))
```

</details>

#### is order sensitive

- Verify: is order sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: is order sensitive")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_pair(1, 2) != hash_pair(2, 1))
```

</details>

### Hash characteristics

#### changes when one character changes

- Verify: changes when one character changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: changes when one character changes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val h1 = hash_text("test")
val h2 = hash_text("tesa")
check(h1 != h2)
```

</details>

#### remains non-zero for non-empty input

- Verify: remains non-zero for non-empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: remains non-zero for non-empty input")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
check(hash_text("sample") != 0)
```

</details>

#### keeps repeated hashing consistent

- Verify: keeps repeated hashing consistent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-HASH_HASH_TRAIT-001
step("Verify: keeps repeated hashing consistent")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val first = hash_array([hash_int(1), hash_int(2), hash_int(3)])
val second = hash_array([hash_int(1), hash_int(2), hash_int(3)])
check(first == second)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9e902e6b3a5c568ced521067c2ee013d0ab9a175ad488d7d3616e8434e597d86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e902e6b3a5c568ced521067c2ee013d0ab9a175ad488d7d3616e8434e597d86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e902e6b3a5c568ced521067c2ee013d0ab9a175ad488d7d3616e8434e597d86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/hash/hash_trait_spec.spl
mirror: doc/06_spec/01_unit/std/hash/hash_trait_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/hash/hash_trait_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/hash/hash_trait_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/hash/hash_trait_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
