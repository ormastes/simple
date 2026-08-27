# Reference Counted Pointers Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reference Counted Pointers Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SHARED-PTR |
| Category | Runtime |
| Status | Implemented |
| Source | `test/feature/usage/shared_pointers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Behaviors

- Reference count incremented on clone, decremented on drop
- Value is deallocated when reference count reaches zero
- Cloning creates shallow copy with incremented reference count

## Scenarios

### Reference Counted Pointers

#### creates pointer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates pointer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates pointer")
val ptr = new * 42
expect ptr == 42
```

</details>

#### pointer arithmetic

- pointer arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pointer arithmetic")
val a = new * 10
val b = new * 5
expect a + b == 15
```

</details>

#### multiple references

- multiple references


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple references")
val a = new * 42
val b = a
expect a + b == 84
```

</details>

### Reference Semantics

#### tracks multiple references

- tracks multiple references


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tracks multiple references")
val list = [1, 2, 3]
val ref1 = list
val ref2 = list
expect ref1.len() == 3
expect ref2.len() == 3
```

</details>

#### clones underlying data

- clones underlying data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("clones underlying data")
val original = [1, 2, 3]
val cloned = original
expect cloned[0] == 1
expect cloned.len() == 3
```

</details>

#### dict references work correctly

- dict references work correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dict references work correctly")
val data = {"key": 42}
val ref = data
expect ref["key"] == 42
```

</details>

### Memory Safety

#### data remains valid while referenced

- data remains valid while referenced


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("data remains valid while referenced")
val data = [1, 2, 3]
val r1 = data
expect r1[0] == 1
```

</details>

#### strings are valid

- strings are valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("strings are valid")
val s = "hello"
val ref = s
expect ref.len() == 5
```

</details>

#### nested data structures work

- nested data structures work


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("nested data structures work")
val outer = [[1, 2], [3, 4]]
val ref = outer
expect ref[0][0] == 1
expect ref[1][1] == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5a7d03a04efbcae8b9dc19fdcd81964dc792929e07965cf3422cde678af77635`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a7d03a04efbcae8b9dc19fdcd81964dc792929e07965cf3422cde678af77635`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a7d03a04efbcae8b9dc19fdcd81964dc792929e07965cf3422cde678af77635`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/shared_pointers_spec.spl
mirror: doc/06_spec/feature/usage/shared_pointers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/shared_pointers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/shared_pointers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/shared_pointers_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates pointer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/shared_pointers_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pointer arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/shared_pointers_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple references' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
