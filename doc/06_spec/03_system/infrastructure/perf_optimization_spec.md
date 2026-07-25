# Perf Optimization Specification

> <details>

<!-- sdn-diagram:id=perf_optimization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=perf_optimization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

perf_optimization_spec -> spipe
perf_optimization_spec -> lib
perf_optimization_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=perf_optimization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Perf Optimization Specification

## Scenarios

### PersistentDict hash-bucketed performance

#### should handle multiple insertions without degradation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = build_persistent_dict(3)
expect(dict.len()).to_equal(3)
```

</details>

#### should retrieve keys from a populated dict correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = build_persistent_dict(3)
expect(dict.get("item_0")).to_equal(0)
expect(dict.get("item_250")).to_equal(2500)
expect(dict.get("item_499")).to_equal(4990)
expect(dict.get("nonexistent")).to_equal(nil)
```

</details>

#### should maintain structural sharing on single-key mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = build_persistent_dict(3)
val dict2 = dict.set("item_250", 999)
# Original unchanged
expect(dict.get("item_250")).to_equal(2500)
# New dict has update
expect(dict2.get("item_250")).to_equal(999)
# Both have same size
expect(dict.len()).to_equal(3)
expect(dict2.len()).to_equal(3)
```

</details>

#### should remove keys correctly

1. var dict = new persistent dict
2. dict = dict set
3. dict = dict set
4. dict = dict set
   - Expected: dict2.len() equals `2`
   - Expected: dict2.get("a") equals `1`
   - Expected: dict2.get("b") equals `nil`
   - Expected: dict2.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = new_persistent_dict()
dict = dict.set("a", 1)
dict = dict.set("b", 2)
dict = dict.set("c", 3)
val dict2 = dict.remove("b")
expect(dict2.len()).to_equal(2)
expect(dict2.get("a")).to_equal(1)
expect(dict2.get("b")).to_equal(nil)
expect(dict2.get("c")).to_equal(3)
```

</details>

#### should support merge of two dicts

1. var d1 = new persistent dict
2. d1 = d1 set
3. d1 = d1 set
4. var d2 = new persistent dict
5. d2 = d2 set
6. d2 = d2 set
   - Expected: merged.len() equals `3`
   - Expected: merged.get("x") equals `1`
   - Expected: merged.get("y") equals `99`
   - Expected: merged.get("z") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d1 = new_persistent_dict()
d1 = d1.set("x", 1)
d1 = d1.set("y", 2)
var d2 = new_persistent_dict()
d2 = d2.set("y", 99)
d2 = d2.set("z", 3)
val merged = d1.merge(d2)
expect(merged.len()).to_equal(3)
expect(merged.get("x")).to_equal(1)
expect(merged.get("y")).to_equal(99)
expect(merged.get("z")).to_equal(3)
```

</details>

### PersistentVec chunked performance

#### should handle multiple pushes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pvec = build_persistent_vec(3)
expect(pvec.len()).to_equal(3)
```

</details>

#### should index correctly across chunk boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pvec = build_persistent_vec(100)
expect(pvec.get(0)).to_equal(0)
expect(pvec.get(31)).to_equal(93)
expect(pvec.get(32)).to_equal(96)
expect(pvec.get(99)).to_equal(297)
```

</details>

#### should pop from chunked vec

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pvec = build_persistent_vec(50)
val vec2 = pvec.pop()
expect(vec2.len()).to_equal(49)
expect(vec2.last()).to_equal(144)
expect(pvec.len()).to_equal(50)
```

</details>

#### should set values correctly across chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pvec = build_persistent_vec(64)
val vec2 = pvec.set(33, 999)
expect(vec2.get(33)).to_equal(999)
expect(pvec.get(33)).to_equal(99)
```

</details>

### Map hash-first comparison

#### should handle negative hash values without crash

1. var map = Map new
2. map insert
3. map insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Keys that might produce negative hashes
var map = Map.new()
map.insert("very_long_key_name_that_might_overflow", 1)
map.insert("another_potentially_negative_hash_key", 2)
expect(map.len()).to_be_greater_than(1)
match map.get("very_long_key_name_that_might_overflow"):
    Some(v): expect(v).to_equal(1)
    nil: expect(true).to_equal(false)
```

</details>

### MIR optimization pipeline

#### should include GVN and TCO in Speed pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify pass registration (structural check)
val pipeline = optimizationpipeline_for_level(OptLevel.Speed)
var has_gvn = false
var has_tco = false
for pass_name in pipeline.passes:
    if pass_name == "global_value_numbering":
        has_gvn = true
    if pass_name == "tail_call_optimization":
        has_tco = true
expect(has_gvn).to_equal(true)
expect(has_tco).to_equal(true)
```

</details>

#### should include GVN and TCO in Aggressive pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = optimizationpipeline_for_level(OptLevel.Aggressive)
var has_gvn = false
var has_tco = false
for pass_name in pipeline.passes:
    if pass_name == "global_value_numbering":
        has_gvn = true
    if pass_name == "tail_call_optimization":
        has_tco = true
expect(has_gvn).to_equal(true)
expect(has_tco).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/perf_optimization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentDict hash-bucketed performance
- PersistentVec chunked performance
- Map hash-first comparison
- MIR optimization pipeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
