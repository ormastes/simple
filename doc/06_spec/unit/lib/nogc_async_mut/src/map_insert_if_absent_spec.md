# map_insert_if_absent_spec

> Purpose and audience: behavioral verification of the nogc_async_mut pure Map

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# map_insert_if_absent_spec

Purpose and audience: behavioral verification of the nogc_async_mut pure Map

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/src/map_insert_if_absent_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: behavioral verification of the nogc_async_mut pure Map
insert_if_absent operation. Scope: inserting missing keys without overwriting
existing values. Audience: stdlib map maintainers.

research: doc/01_research/lib/collections_impl/collections.md ; plan: doc/03_plan/lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16_tldr.md ; architecture: doc/04_architecture/lib/runtime_family_stdlib_surface.md ; design: doc/05_design/lib/stdlib/aop_support_matrix.md

## Scenarios

### nogc_async_mut pure Map insert_if_absent

#### inserts missing keys without overwriting existing values

- Insert a missing key and confirm it lands
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: map.insert_if_absent("name", 1) is true
   - Expected: map.len() equals `1`
   - Expected: map.get("name")? equals `1`
- Retry the same key and confirm the stored value is preserved
   - Expected: map.insert_if_absent("name", 2) is false
   - Expected: map.len() equals `1`
   - Expected: map.get("name")? equals `1`
- Insert a second distinct key
   - Expected: map.insert_if_absent("other", 3) is true
   - Expected: map.len() equals `2`
   - Expected: map.get("other")? equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-MAP-INSERT-IF-ABSENT
step("Insert a missing key and confirm it lands")
var map: Map<text, i32> = Map.new()

expect(map.insert_if_absent("name", 1)).to_equal(true)
expect(map.len()).to_equal(1)  # oracle: 1 = single key inserted so far (or retry added no entry)
expect(map.get("name")?).to_equal(1)  # oracle: 1 = value stored by the first insert (or preserved after rejected retry)

step("Retry the same key and confirm the stored value is preserved")
expect(map.insert_if_absent("name", 2)).to_equal(false)
expect(map.len()).to_equal(1)  # oracle: 1 = single key inserted so far (or retry added no entry)
expect(map.get("name")?).to_equal(1)  # oracle: 1 = value stored by the first insert (or preserved after rejected retry)

step("Insert a second distinct key")
expect(map.insert_if_absent("other", 3)).to_equal(true)
expect(map.len()).to_equal(2)  # oracle: 2 = both distinct keys now present
expect(map.get("other")?).to_equal(3)  # oracle: 3 = value stored for the second distinct key
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-LIB-MAP-INSERT-IF-ABSENT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a91593e249b5b705bccac215aec765b5a259ad8cf5de9679618963e59699000`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a91593e249b5b705bccac215aec765b5a259ad8cf5de9679618963e59699000`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a91593e249b5b705bccac215aec765b5a259ad8cf5de9679618963e59699000`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: unit/lib/nogc_async_mut/src/map_insert_if_absent_spec.spl
mirror: src/map_insert_if_absent_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
src/map_insert_if_absent_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
src/map_insert_if_absent_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
