# Map/dict for_each Traversal Specification

> `Map<K, V>` lowers to the builtin `dict`. Until 2026-08-21 the seed's dict

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Map/dict for_each Traversal Specification

`Map<K, V>` lowers to the builtin `dict`. Until 2026-08-21 the seed's dict

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/map_for_each_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# Map/dict for_each Traversal Specification

`Map<K, V>` lowers to the builtin `dict`. Until 2026-08-21 the seed's dict
method table had no traversal method at all, so `map.for_each(\k, v: ...)`
failed with `method 'for_each' not found on type 'dict'` while the array form
worked. Regression cover for
doc/08_tracking/bug/map_for_each_missing_on_dict_2026-08-21.md and item 4 of
doc/08_tracking/bug/interpreter_raw_array_and_glob_import_gaps_2026-08-21.md.

Two properties are asserted together, because either alone would let the
method exist and still be useless:
  * the traversal RUNS (every entry visited exactly once), and
  * a side effect on a variable of the ENCLOSING scope survives the call —
    accumulating into an outer `var` is the whole point of `for_each`, and a
    body evaluated against a detached copy of the closure environment would
    make every such call a silent no-op.

## Scenarios

### map for_each traversal

#### visits every entry exactly once

- Verify: visits every entry exactly once
   - Expected: visits equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_MAP_FOR_EACH-001
step("Verify: visits every entry exactly once")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var m: {i64: i64} = {}
m[1] = 10
m[2] = 20
m[3] = 30
var visits = 0
m.for_each(\k, v:
    visits = visits + 1
)
expect(visits).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### accumulates into a variable of the enclosing scope

- Verify: accumulates into a variable of the enclosing scope
   - Expected: total equals `60)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_MAP_FOR_EACH-001
step("Verify: accumulates into a variable of the enclosing scope")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var m: {i64: i64} = {}
m[1] = 10
m[2] = 20
m[3] = 30
var total = 0
m.for_each(\k, v:
    total = total + v
)
expect(total).to_equal(60)  # oracle: pinned constant asserted by this scenario
```

</details>

#### passes both the key and the value to a two-parameter lambda

- Verify: passes both the key and the value to a two-parameter lambda
   - Expected: keys_seen equals `1;2;`
   - Expected: value_sum equals `30)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_MAP_FOR_EACH-001
step("Verify: passes both the key and the value to a two-parameter lambda")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# The key arrives in the SAME representation `keys()` and `entries()`
# use -- for a scalar `i64` key that is its text form, not an `i64`
# (`m.keys()` likewise yields "1", so `k + 1` concatenates). That is a
# pre-existing property of the dict surface, asserted here as-is so
# for_each cannot silently drift away from its sibling accessors.
var m: {i64: i64} = {}
m[1] = 10
m[2] = 20
var keys_seen = ""
var value_sum = 0
m.for_each(\k, v:
    keys_seen = keys_seen + "{k};"
    value_sum = value_sum + v
)
expect(keys_seen).to_equal("1;2;")
expect(value_sum).to_equal(30)  # oracle: pinned constant asserted by this scenario
```

</details>

#### supports `each` as an alias for `for_each`

- Verify: supports each as an alias for for_each
   - Expected: total equals `12)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_MAP_FOR_EACH-001
step("Verify: supports each as an alias for for_each")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var m: {i64: i64} = {}
m[1] = 4
m[2] = 8
var total = 0
m.each(\k, v:
    total = total + v
)
expect(total).to_equal(12)  # oracle: pinned constant asserted by this scenario
```

</details>

#### visits entries in the same order as keys()

- Verify: visits entries in the same order as keys()
   - Expected: seen equals `m.keys()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_MAP_FOR_EACH-001
step("Verify: visits entries in the same order as keys()")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# for_each must agree with the dict's canonical iteration order, or a
# traversal written with for_each and one written with a for loop
# disagree about ordering.
var m: {i64: i64} = {}
m[3] = 30
m[1] = 10
m[2] = 20
var seen: [i64] = []
m.for_each(\k, v:
    seen = seen.push(k)
)
expect(seen).to_equal(m.keys())
```

</details>

<details>
<summary>Advanced: does not leak its loop variables into the caller's scope</summary>

#### does not leak its loop variables into the caller's scope

- Verify: does not leak its loop variables into the caller's scope
   - Expected: k equals `999)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_MAP_FOR_EACH-001
step("Verify: does not leak its loop variables into the caller's scope")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var m: {i64: i64} = {}
m[1] = 10
val k = 999
var total = 0
m.for_each(\k, v:
    total = total + v
)
expect(k).to_equal(999)  # oracle: pinned constant asserted by this scenario
```

</details>


</details>

#### leaves the receiver unchanged

- Verify: leaves the receiver unchanged
   - Expected: m.len() equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_MAP_FOR_EACH-001
step("Verify: leaves the receiver unchanged")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var m: {i64: i64} = {}
m[1] = 10
m[2] = 20
var total = 0
m.for_each(\k, v:
    total = total + v
)
expect(m.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### is a no-op on an empty map

- Verify: is a no-op on an empty map
   - Expected: visits equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_MAP_FOR_EACH-001
step("Verify: is a no-op on an empty map")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var m: {i64: i64} = {}
var visits = 0
m.for_each(\k, v:
    visits = visits + 1
)
expect(visits).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `86cfee1a8c2a48550d715b7dfb4ef8b894221451a0a8a209cac82af62f8659d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86cfee1a8c2a48550d715b7dfb4ef8b894221451a0a8a209cac82af62f8659d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86cfee1a8c2a48550d715b7dfb4ef8b894221451a0a8a209cac82af62f8659d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/map_for_each_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/map_for_each_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/map_for_each_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_sync_mut/map_for_each_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/map_for_each_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
