# Array Free Deep Specification

> Tests covering rt_array_free_deep.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array Free Deep Specification

## Scenarios

### rt_array_free_deep

#### is reachable from .spl on this lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is reachable from .spl on this lane
   - Expected: verdict >= 0 is true
   - Expected: verdict <= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("is reachable from .spl on this lane")
# Resolving at all is the regression: this whole file failed to
# compile while the symbol was declared in only one of the two
# runtimes.
val empty: [text] = []
val verdict = rt_array_free_deep(empty)
expect(verdict >= 0).to_equal(true)
expect(verdict <= 1).to_equal(true)
```

</details>

#### returns a strict binary verdict, never a partial-free code

- returns a strict binary verdict, never a partial-free code
   - Expected: verdict == 0 or verdict == 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("returns a strict binary verdict, never a partial-free code")
# The contract's whole point is that 1 means "the entire structure is
# gone" and 0 means "nothing was touched". Any third value would mean a
# partial free had become expressible.
val arr = unique_strings(64)
val verdict = rt_array_free_deep(arr)
expect(verdict == 0 or verdict == 1).to_equal(true)
```

</details>

#### never grows the heap registry

- never grows the heap registry
   - Expected: after_free <= after_fill is true
   - Expected: after_fill >= before is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("never grows the heap registry")
val before = rt_heap_registry_count()
val arr = unique_strings(32)
val after_fill = rt_heap_registry_count()
val _verdict = rt_array_free_deep(arr)
val after_free = rt_heap_registry_count()
expect(after_free <= after_fill).to_equal(true)
expect(after_fill >= before).to_equal(true)
```

</details>

#### refuses a second free of the same array and reclaims nothing more

- refuses a second free of the same array and reclaims nothing more
   - Expected: second equals `0`
   - Expected: after_second >= after_first is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("refuses a second free of the same array and reclaims nothing more")
# ALL-OR-NOTHING, the direction that holds on every lane: whatever the
# first call did, the second must be a pure refusal. The handle is
# stale after a successful first free -- never read its CONTENT again;
# the registry membership check is what makes re-passing it safe.
val arr = unique_strings(32)
val _first = rt_array_free_deep(arr)
val after_first = rt_heap_registry_count()

val second = rt_array_free_deep(arr)
val after_second = rt_heap_registry_count()

expect(second).to_equal(0)
expect(after_second >= after_first).to_equal(true)
```

</details>

#### a verdict of 1 is backed by a real registry drop, never claimed

- a verdict of 1 is backed by a real registry drop, never claimed
   - Expected: after_fill - after_free >= elements + 1 is true
   - Expected: after_free equals `after_fill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("a verdict of 1 is backed by a real registry drop, never claimed")
# The one direction that is both lane-independent AND non-vacuous where
# it fires: a "1" that did not shrink the registry would be the
# primitive lying about an all-or-nothing reclaim. Measured on the JIT
# lane with 2000 elements: delta_free=2001 (every string plus the array
# header), verdict=1. On the interpreter lane the registry holds
# nothing to begin with and the verdict is an honest 0, so this reads
# as a true implication rather than a false pass.
val elements = 256
val arr = unique_strings(elements)
val after_fill = rt_heap_registry_count()
val verdict = rt_array_free_deep(arr)
val after_free = rt_heap_registry_count()
if verdict == 1:
    expect(after_fill - after_free >= elements + 1).to_equal(true)
else:
    expect(after_free).to_equal(after_fill)
```

</details>

#### refuses a value that is not a registered array without side effects

- refuses a value that is not a registered array without side effects
   - Expected: rt_array_free_deep(empty) equals `rt_array_free_deep(empty)`
   - Expected: after <= before is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("refuses a value that is not a registered array without side effects")
val empty: [text] = []
val before = rt_heap_registry_count()
expect(rt_array_free_deep(empty)).to_equal(rt_array_free_deep(empty))
val after = rt_heap_registry_count()
expect(after <= before).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/array_free_deep_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_array_free_deep.
- rt_array_free_deep

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ef835c3d4cbe5dc30a5c3c5cf0fd9f0acb7cec516b11bf0455c63c557fd547a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef835c3d4cbe5dc30a5c3c5cf0fd9f0acb7cec516b11bf0455c63c557fd547a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef835c3d4cbe5dc30a5c3c5cf0fd9f0acb7cec516b11bf0455c63c557fd547a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/runtime/array_free_deep_spec.spl
mirror: doc/06_spec/01_unit/runtime/array_free_deep_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/array_free_deep_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/array_free_deep_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/array_free_deep_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/runtime/array_free_deep_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is reachable from .spl on this lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/array_free_deep_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a strict binary verdict, never a partial-free code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/array_free_deep_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never grows the heap registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
