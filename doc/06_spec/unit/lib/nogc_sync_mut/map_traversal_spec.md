# Map Traversal Specification

> Tests covering nogc_sync_mut Map traversal helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Map Traversal Specification

## Scenarios

### nogc_sync_mut Map traversal helpers

#### filters entries without changing source map

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- filters entries without changing source map


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters entries without changing source map")
var map: Map<i64, i64> = Map.new()
map.insert(1, 1)
map.insert(2, 2)
map.insert(3, 3)

val filtered = map.filter(\key, value: value >= 2)

expect filtered.has(1) to_equal false
expect filtered.get(2).unwrap() to_equal 2
expect filtered.get(3).unwrap() to_equal 3
expect map.len() to_equal 3
```

</details>

#### maps values while preserving keys

- maps values while preserving keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps values while preserving keys")
var map: Map<i64, i64> = Map.new()
map.insert(1, 4)
map.insert(2, 7)

val mapped = map.map_values(_1 * 10)

expect mapped.get(1).unwrap() to_equal 40
expect mapped.get(2).unwrap() to_equal 70
expect map.get(1).unwrap() to_equal 4
```

</details>

#### visits each entry exactly once

- visits each entry exactly once


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("visits each entry exactly once")
var map: Map<i64, i64> = Map.new()
map.insert(1, 1)
map.insert(2, 2)
var total = 0
var count = 0

map.for_each(\key, value:
    total = total + value
    count = count + 1
)

expect total to_equal 3
expect count to_equal 2
```

</details>

#### merges entries from another map

- merges entries from another map


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges entries from another map")
var left: Map<i64, i64> = Map.new()
left.insert(1, 1)
left.insert(2, 2)
var right: Map<i64, i64> = Map.new()
right.insert(2, 20)
right.insert(3, 30)

left.merge(right)

expect left.get(1).unwrap() to_equal 1
expect left.get(2).unwrap() to_equal 20
expect left.get(3).unwrap() to_equal 30
expect left.len() to_equal 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_sync_mut/map_traversal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_sync_mut Map traversal helpers.
- nogc_sync_mut Map traversal helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `5dca5cb1ae457189b5dcedea55579118bdca22ae02ff0d1d36715c8c6b445e63`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5dca5cb1ae457189b5dcedea55579118bdca22ae02ff0d1d36715c8c6b445e63`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5dca5cb1ae457189b5dcedea55579118bdca22ae02ff0d1d36715c8c6b445e63`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_sync_mut/map_traversal_spec.spl
mirror: doc/06_spec/unit/lib/nogc_sync_mut/map_traversal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_sync_mut/map_traversal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_sync_mut/map_traversal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_sync_mut/map_traversal_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters entries without changing source map' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_sync_mut/map_traversal_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps values while preserving keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_sync_mut/map_traversal_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'visits each entry exactly once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
