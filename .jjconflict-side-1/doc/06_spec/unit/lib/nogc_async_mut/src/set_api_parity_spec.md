# set_api_parity_spec

> Purpose and audience: API-parity verification for the nogc_async_mut pure Set

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# set_api_parity_spec

Purpose and audience: API-parity verification for the nogc_async_mut pure Set

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/src/set_api_parity_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: API-parity verification for the nogc_async_mut pure Set
container. Scope: construction, membership, enumeration, subset/superset, and
binary set-operation aliases. Audience: stdlib set maintainers.

research: doc/01_research/lib/collections_impl/collections.md ; plan: doc/03_plan/lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16_tldr.md ; architecture: doc/04_architecture/lib/runtime_family_stdlib_surface.md ; design: doc/05_design/lib/stdlib/aop_support_matrix.md

## Scenarios

### nogc_async_mut pure Set API parity

#### supports construction, membership, and enumeration aliases

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Construction, membership, and enumeration (expected show, folded, detail, or skip)


- Construct from a duplicate-bearing array and check size
   - Text capture: after_step
   - Evidence: text output verified by 6 expected checks
   - Expected: set.size() equals `3`
   - Expected: set contains `1`
   - Expected: set.has(2) is true
   - Expected: set contains `3`
   - Expected: set.to_list().len() equals `3`
   - Expected: array_set.to_array().len() equals `3`
- Add, remove, clone, and clear
   - Expected: added.add(3) is true
   - Expected: added contains `3`
   - Expected: added.remove(2) is true
   - Expected: not_contains_2 is true
   - Expected: added.to_array().len() equals `2`
   - Expected: cloned contains `1`
   - Expected: cloned contains `3`
   - Expected: added.size() equals `0`
   - Expected: added.to_array().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-SET-API-PARITY
step("Construct from a duplicate-bearing array and check size")
var set = Set.from_array([1, 2, 1, 3])
expect(set.size()).to_equal(3)  # oracle: 3 = distinct elements of {1,2,1,3}
expect(set.contains(1)).to_equal(true)
expect(set.has(2)).to_equal(true)
expect(set.contains(3)).to_equal(true)
expect(set.to_list().len()).to_equal(3)  # oracle: 3 = enumeration yields each distinct element once

var array_set = Set.from_array([1, 2, 1, 3])
expect(array_set.to_array().len()).to_equal(3)

step("Add, remove, clone, and clear")
var added = Set.from_array([1, 2])
expect(added.add(3)).to_equal(true)
expect(added.contains(3)).to_equal(true)

expect(added.remove(2)).to_equal(true)
val not_contains_2 = not added.contains(2)
expect(not_contains_2).to_equal(true)
expect(added.to_array().len()).to_equal(2)  # oracle: 2 = {1,3} remain after removing 2

val cloned = added.clone()
expect(cloned.contains(1)).to_equal(true)
expect(cloned.contains(3)).to_equal(true)

added.clear()
expect(added.size()).to_equal(0)  # oracle: 0 = clear empties the set
expect(added.to_array().len()).to_equal(0)
```

</details>

#### supports subset and superset aliases

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Subset and superset relations (expected show, folded, detail, or skip)


- Check subset and superset relations in both directions
   - Text capture: after_step
   - Evidence: text output verified by 4 expected checks
   - Expected: subset.is_subset(superset) is true
   - Expected: superset.is_superset(subset) is true
   - Expected: super_not_subset is true
   - Expected: sub_not_superset is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-SET-API-PARITY
step("Check subset and superset relations in both directions")
val subset = Set.from_array([2])
val superset = Set.from_array([1, 2, 3])
expect(subset.is_subset(superset)).to_equal(true)
expect(superset.is_superset(subset)).to_equal(true)
val super_not_subset = not superset.is_subset(subset)
expect(super_not_subset).to_equal(true)
val sub_not_superset = not subset.is_superset(superset)
expect(sub_not_superset).to_equal(true)
```

</details>

#### supports binary set operation aliases

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Binary set operations (expected show, folded, detail, or skip)


- Compute union, intersection, difference, and symmetric difference
   - Text capture: after_step
   - Evidence: text output verified by 9 expected checks
   - Expected: union_set contains `1`
   - Expected: union_set contains `4`
   - Expected: intersection_set contains `2`
   - Expected: intersect_not_1 is true
   - Expected: difference_set contains `1`
   - Expected: diff_not_2 is true
   - Expected: symmetric_set contains `1`
   - Expected: symmetric_set contains `4`
   - Expected: sym_not_2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-SET-API-PARITY
step("Compute union, intersection, difference, and symmetric difference")
val left = Set.from_array([1, 2, 3])
val right = Set.from_array([2, 4])

val union_set = left.union(right)
expect(union_set.contains(1)).to_equal(true)
expect(union_set.contains(4)).to_equal(true)

val intersection_set = left.intersection(right)
expect(intersection_set.contains(2)).to_equal(true)
val intersect_not_1 = not intersection_set.contains(1)
expect(intersect_not_1).to_equal(true)

val difference_set = left.difference(right)
expect(difference_set.contains(1)).to_equal(true)
val diff_not_2 = not difference_set.contains(2)
expect(diff_not_2).to_equal(true)

val symmetric_set = left.symmetric_difference(right)
expect(symmetric_set.contains(1)).to_equal(true)
expect(symmetric_set.contains(4)).to_equal(true)
val sym_not_2 = not symmetric_set.contains(2)
expect(sym_not_2).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-LIB-SET-API-PARITY`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `02187d07913e40b6987d7c4c69bec8438ed99a094dac3e5e8b04472274584115`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02187d07913e40b6987d7c4c69bec8438ed99a094dac3e5e8b04472274584115`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02187d07913e40b6987d7c4c69bec8438ed99a094dac3e5e8b04472274584115`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: unit/lib/nogc_async_mut/src/set_api_parity_spec.spl
mirror: src/set_api_parity_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
src/set_api_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
src/set_api_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
src/set_api_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
