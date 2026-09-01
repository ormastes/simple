# src_collections_facade_spec

> Purpose: this manual pins the behavior named "nogc_async_mut src collections facade":

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# src_collections_facade_spec

Purpose: this manual pins the behavior named "nogc_async_mut src collections facade":

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/src/collections/src_collections_facade_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: this manual pins the behavior named "nogc_async_mut src collections facade":
" for the owning engineering team.
    Audience: engineers verifying regressions in this area; steps below are executable evidence.

## Scenarios

### nogc_async_mut src collections facade

#### re-exports hash map, hash set, and btree map behavior

- re-exports hash map, hash set, and btree map behavior
   - Expected: map.is_empty() is true
   - Expected: map.insert_if_absent("a", "one") is true
   - Expected: map.insert_if_absent("a", "changed") is false
   - Expected: map.get("a").unwrap() equals `one`
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
   - Expected: set.insert("red") is true
   - Expected: set.insert("red") is false
   - Expected: set contains `red`
   - Expected: set.remove("red") is true
   - Expected: union_set.len() equals `3`
   - Expected: union_set contains `red`
   - Expected: union_set contains `blue`
   - Expected: union_set contains `green`
   - Expected: intersection.len() equals `1`
   - Expected: intersection contains `blue`
   - Expected: difference.len() equals `1`
   - Expected: difference contains `red`
   - Expected: symmetric.len() equals `2`
   - Expected: symmetric contains `red`
   - Expected: symmetric contains `green`
   - Expected: intersection.is_subset(union_set) is true
   - Expected: union_set.is_superset(intersection) is true
   - Expected: left.to_array().len() equals `2`
   - Expected: mapped contains `red!`
   - Expected: filtered.len() equals `2`
   - Expected: reserved_set.insert("cap") is true
   - Expected: reserved_set contains `cap`
   - Expected: tree.first_key().unwrap() equals `a`
   - Expected: tree.last_key().unwrap() equals `b`
   - Expected: tree.get("b").unwrap() equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports hash map, hash set, and btree map behavior")
var map = HashMap.new()
expect(map.is_empty()).to_equal(true)
expect(map.insert_if_absent("a", "one")).to_equal(true)
expect(map.insert_if_absent("a", "changed")).to_equal(false)
expect(map.get("a").unwrap()).to_equal("one")
map.insert("a", "one")
map.insert("b", "two")
map.insert("Z9!", "wide")
expect(map.len()).to_equal(3)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(map.get("a").unwrap()).to_equal("one")
expect(map.has("b")).to_equal(true)
expect(map.get("Z9!").unwrap()).to_equal("wide")
expect(map.entries().len()).to_equal(3)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
val mapped_values = map.map_values(_1 + "!")
expect(mapped_values.get("b").unwrap()).to_equal("two!")
val filtered_map = map.filter(\key, value: key != "a" and value != "wide")
expect(filtered_map.len()).to_equal(1)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(filtered_map.get("b").unwrap()).to_equal("two")
var reserved_map = HashMap.with_capacity(64)
reserved_map.insert("cap", "ok")
expect(reserved_map.get("cap").unwrap()).to_equal("ok")
expect(map.remove("a").unwrap()).to_equal("one")

var set = HashSet.new()
expect(set.insert("red")).to_equal(true)
expect(set.insert("red")).to_equal(false)
expect(set.contains("red")).to_equal(true)
expect(set.remove("red")).to_equal(true)

var left = HashSet.new()
left.insert("red")
left.insert("blue")
var right = HashSet.new()
right.insert("blue")
right.insert("green")
val union_set = left.union(right)
expect(union_set.len()).to_equal(3)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(union_set.contains("red")).to_equal(true)
expect(union_set.contains("blue")).to_equal(true)
expect(union_set.contains("green")).to_equal(true)
val intersection = left.intersection(right)
expect(intersection.len()).to_equal(1)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(intersection.contains("blue")).to_equal(true)
val difference = left.difference(right)
expect(difference.len()).to_equal(1)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(difference.contains("red")).to_equal(true)
val symmetric = left.symmetric_difference(right)
expect(symmetric.len()).to_equal(2)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(symmetric.contains("red")).to_equal(true)
expect(symmetric.contains("green")).to_equal(true)
expect(intersection.is_subset(union_set)).to_equal(true)
expect(union_set.is_superset(intersection)).to_equal(true)
expect(left.to_array().len()).to_equal(2)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
val mapped = left.map(_1 + "!")
expect(mapped.contains("red!")).to_equal(true)
val filtered = union_set.filter(_1 != "green")
expect(filtered.len()).to_equal(2)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
var reserved_set = HashSet.with_capacity(64)
expect(reserved_set.insert("cap")).to_equal(true)
expect(reserved_set.contains("cap")).to_equal(true)

var tree = BTreeMap.new()
tree.insert("b", "two")
tree.insert("a", "one")
expect(tree.first_key().unwrap()).to_equal("a")
expect(tree.last_key().unwrap()).to_equal("b")
expect(tree.get("b").unwrap()).to_equal("two")

# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `edc8192440e60ec5ea6e344bf819b01a36e1f4963d9d0d1ba6e93a1658261200`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `edc8192440e60ec5ea6e344bf819b01a36e1f4963d9d0d1ba6e93a1658261200`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `edc8192440e60ec5ea6e344bf819b01a36e1f4963d9d0d1ba6e93a1658261200`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/lib/nogc_async_mut/src/collections/src_collections_facade_spec.spl
mirror: src/collections/src_collections_facade_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
src/collections/src_collections_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
src/collections/src_collections_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
