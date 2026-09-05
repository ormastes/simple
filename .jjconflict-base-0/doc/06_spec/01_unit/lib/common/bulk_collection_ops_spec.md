# Bulk Collection Ops Specification

> Tests covering map_join, filter_map_join, map_to_text, enumerate_join.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bulk Collection Ops Specification

## Scenarios

### map_join

#### maps and joins with separator

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps and joins with separator
   - Expected: result equals `1, 2, 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps and joins with separator")
val result = map_join([1, 2, 3], "{_1}", ", ")
expect(result).to_equal("1, 2, 3")
```

</details>

#### handles empty array

- handles empty array
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty array")
val result = map_join([], "{_1}", ", ")
expect(result).to_equal("")
```

</details>

#### handles single element

- handles single element
   - Expected: result equals `num=42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single element")
val result = map_join([42], "num={_1}", ", ")
expect(result).to_equal("num=42")
```

</details>

#### works with transform function

- works with transform function
   - Expected: result equals `10-20-30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with transform function")
val result = map_join([1, 2, 3], \x: "{x * 10}", "-")
expect(result).to_equal("10-20-30")
```

</details>

### filter_map_join

#### filters then maps then joins

- filters then maps then joins
   - Expected: result equals `3, 4, 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters then maps then joins")
val result = filter_map_join([1, 2, 3, 4, 5], _1 > 2, "{_1}", ", ")
expect(result).to_equal("3, 4, 5")
```

</details>

#### handles all filtered out

- handles all filtered out
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all filtered out")
val result = filter_map_join([1, 2, 3], _1 > 10, "{_1}", ", ")
expect(result).to_equal("")
```

</details>

#### handles none filtered out

- handles none filtered out
   - Expected: result equals `v1+v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles none filtered out")
val result = filter_map_join([1, 2], _1 > 0, "v{_1}", "+")
expect(result).to_equal("v1+v2")
```

</details>

### map_to_text

#### maps and concatenates without separator

- maps and concatenates without separator
   - Expected: result equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps and concatenates without separator")
val result = map_to_text([1, 2, 3], "{_1}")
expect(result).to_equal("123")
```

</details>

#### handles empty array

- handles empty array
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty array")
val result = map_to_text([], "{_1}")
expect(result).to_equal("")
```

</details>

#### works with text transform

- works with text transform
   - Expected: result equals `[a][b][c]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with text transform")
val result = map_to_text(["a", "b", "c"], "[{_1}]")
expect(result).to_equal("[a][b][c]")
```

</details>

### enumerate_join

#### provides element and index

- provides element and index
   - Expected: result equals `0:a, 1:b, 2:c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides element and index")
val result = enumerate_join(["a", "b", "c"], \elem, i: "{i}:{elem}", ", ")
expect(result).to_equal("0:a, 1:b, 2:c")
```

</details>

#### handles empty array

- handles empty array
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty array")
val result = enumerate_join([], \elem, i: "{i}:{elem}", ", ")
expect(result).to_equal("")
```

</details>

#### handles single element

- handles single element
   - Expected: result equals `0=only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single element")
val result = enumerate_join(["only"], \elem, i: "{i}={elem}", ", ")
expect(result).to_equal("0=only")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bulk_collection_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering map_join, filter_map_join, map_to_text, enumerate_join.
- map_join
- filter_map_join
- map_to_text
- enumerate_join

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `919747c2df354dbd0ef7f16d7f455ebfe6040e3f984585ce949fe2dd1f9886fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `919747c2df354dbd0ef7f16d7f455ebfe6040e3f984585ce949fe2dd1f9886fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `919747c2df354dbd0ef7f16d7f455ebfe6040e3f984585ce949fe2dd1f9886fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/bulk_collection_ops_spec.spl
mirror: doc/06_spec/01_unit/lib/common/bulk_collection_ops_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/bulk_collection_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/bulk_collection_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/bulk_collection_ops_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps and joins with separator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/bulk_collection_ops_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/bulk_collection_ops_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles single element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
