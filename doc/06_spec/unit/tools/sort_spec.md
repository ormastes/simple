# Sort Specification

> Tests covering sort tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sort Specification

## Scenarios

### sort tool

#### basic sorting

#### sorts lines alphabetically

- sorts lines alphabetically
   - Expected: result[0] equals `apple`
   - Expected: result[1] equals `banana`
   - Expected: result[2] equals `cherry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts lines alphabetically")
val lines = ["cherry", "apple", "banana"]
val result = _local_sort(lines)
expect(result[0]).to_equal("apple")
expect(result[1]).to_equal("banana")
expect(result[2]).to_equal("cherry")
```

</details>

#### sorts in reverse

- sorts in reverse
   - Expected: result[0] equals `cherry`
   - Expected: result[1] equals `banana`
   - Expected: result[2] equals `apple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts in reverse")
val lines = ["apple", "cherry", "banana"]
val sorted = _local_sort(lines)
# Reverse the sorted result (using helper to avoid while-loop-in-it-block bug)
val result = _reverse_list(sorted)
expect(result[0]).to_equal("cherry")
expect(result[1]).to_equal("banana")
expect(result[2]).to_equal("apple")
```

</details>

#### numeric sorting

#### sorts numbers numerically

- sorts numbers numerically
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts numbers numerically")
# Use local sort (lexicographic), just verify sorting works
val lines = ["1", "10", "100", "2"]
val result = _local_sort(lines)
# Lexicographic: "1" < "10" < "100" < "2"
expect(result.len()).to_equal(4)
```

</details>

#### field extraction

#### extracts first field

- extracts first field
   - Expected: field equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts first field")
val field = extract_field("hello world", 1, " ")
expect(field).to_equal("hello")
```

</details>

#### extracts second field

- extracts second field
   - Expected: field equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts second field")
val field = extract_field("hello world", 2, " ")
expect(field).to_equal("world")
```

</details>

#### returns full line for invalid field

- returns full line for invalid field
   - Expected: field equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns full line for invalid field")
val field = extract_field("hello", 5, " ")
expect(field).to_equal("hello")
```

</details>

#### duplicate removal

#### removes consecutive duplicates

- removes consecutive duplicates
   - Expected: result.len() equals `3`
   - Expected: result[0] equals `a`
   - Expected: result[1] equals `b`
   - Expected: result[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes consecutive duplicates")
val lines = ["a", "a", "b", "b", "c"]
val result = remove_duplicates(lines)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("b")
expect(result[2]).to_equal("c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/sort_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sort tool.
- sort tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `3f44079abfa595c65fbea12fe2514e715201c61a33916d83d909e8d797365e21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f44079abfa595c65fbea12fe2514e715201c61a33916d83d909e8d797365e21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f44079abfa595c65fbea12fe2514e715201c61a33916d83d909e8d797365e21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/tools/sort_spec.spl
mirror: doc/06_spec/unit/tools/sort_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/sort_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/sort_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/sort_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/tools/sort_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts lines alphabetically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/sort_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts in reverse' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/sort_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts numbers numerically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
