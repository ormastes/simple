# src_collections_facade_spec

> Purpose and audience: facade smoke verification for the gc_async_mut src

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# src_collections_facade_spec

Purpose and audience: facade smoke verification for the gc_async_mut src

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/src/collections/src_collections_facade_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: facade smoke verification for the gc_async_mut src
collections modules. Scope: HashMap, HashSet, and BTreeMap behavior reachable
through the facade re-exports. Audience: stdlib collections maintainers.

research: doc/01_research/lib/collections_impl/collections.md ; plan: doc/03_plan/lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16_tldr.md ; architecture: doc/04_architecture/lib/runtime_family_stdlib_surface.md ; design: doc/05_design/lib/stdlib/aop_support_matrix.md
requirements: doc/02_requirements/language/collections/hashmap_basic.md

## Scenarios

### gc_async_mut src collections facade

#### re-exports hash map, hash set, and btree map behavior

- Exercise HashMap insert, get, map_values, filter, and remove
   - Text capture: after_step
   - Evidence: text output verified by 11 expected checks
   - Expected: map.is_empty() is true
   - Expected: map.len() equals `3`
   - Expected: map.get("a").unwrap() equals `one`
   - Expected: map.has("b") is true
   - Expected: map.get("Z9!").unwrap() equals `wide`
   - Expected: map.entries().len() equals `3`
   - Expected: mapped_values.get("b").unwrap() equals `two!`
   - Expected: filtered_map.len() equals `1`
   - Expected: filtered_map.get("b").unwrap() equals `two`
   - Expected: reserved_map.get("cap").unwrap() equals `ok`
   - Expected: map.remove("a").unwrap() equals `one`
- Exercise HashSet insert, contains, and remove
   - Expected: set.insert("red") is true
   - Expected: set.insert("red") is false
   - Expected: set contains `red`
   - Expected: set.remove("red") is true
   - Expected: reserved_set.insert("cap") is true
   - Expected: reserved_set contains `cap`
- Exercise BTreeMap ordered key access
   - Expected: tree.first_key().unwrap() equals `a`
   - Expected: tree.last_key().unwrap() equals `b`
   - Expected: tree.get("b").unwrap() equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LIB-COLLECTIONS-FACADE
step("Exercise HashMap insert, get, map_values, filter, and remove")
var map = HashMap.new()
expect(map.is_empty()).to_equal(true)
map.insert("a", "one")
map.insert("b", "two")
map.insert("Z9!", "wide")
expect(map.len()).to_equal(3)  # oracle: 3 = one entry per insert ("a", "b", "Z9!")
expect(map.get("a").unwrap()).to_equal("one")
expect(map.has("b")).to_equal(true)
expect(map.get("Z9!").unwrap()).to_equal("wide")
expect(map.entries().len()).to_equal(3)  # oracle: 3 = every inserted key appears once as an entry
val mapped_values = map.map_values(_1 + "!")
expect(mapped_values.get("b").unwrap()).to_equal("two!")
val filtered_map = map.filter(\key, value: key != "a" and value != "wide")
expect(filtered_map.len()).to_equal(1)  # oracle: 1 = only "b" survives the filter
expect(filtered_map.get("b").unwrap()).to_equal("two")
var reserved_map = HashMap.with_capacity(64)
reserved_map.insert("cap", "ok")
expect(reserved_map.get("cap").unwrap()).to_equal("ok")
expect(map.remove("a").unwrap()).to_equal("one")

step("Exercise HashSet insert, contains, and remove")
var set = HashSet.new()
expect(set.insert("red")).to_equal(true)
expect(set.insert("red")).to_equal(false)
expect(set.contains("red")).to_equal(true)
expect(set.remove("red")).to_equal(true)
var reserved_set = HashSet.with_capacity(64)
expect(reserved_set.insert("cap")).to_equal(true)
expect(reserved_set.contains("cap")).to_equal(true)

step("Exercise BTreeMap ordered key access")
var tree = BTreeMap.new()
tree.insert("b", "two")
tree.insert("a", "one")
expect(tree.first_key().unwrap()).to_equal("a")
expect(tree.last_key().unwrap()).to_equal("b")
expect(tree.get("b").unwrap()).to_equal("two")
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

- `REQ-LIB-COLLECTIONS-FACADE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37ba77494f3b6aaa1f1466ddc3227117f6543ba86a889bce3de626f97ed5ea0f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37ba77494f3b6aaa1f1466ddc3227117f6543ba86a889bce3de626f97ed5ea0f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37ba77494f3b6aaa1f1466ddc3227117f6543ba86a889bce3de626f97ed5ea0f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: unit/lib/gc_async_mut/src/collections/src_collections_facade_spec.spl
mirror: src/collections/src_collections_facade_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
src/collections/src_collections_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
src/collections/src_collections_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
