# map_correctness_spec

> Verifies the map correctness behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# map_correctness_spec

Verifies the map correctness behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/map/map_correctness_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the map correctness behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Map correctness

#### creates an empty map

- Verify: creates an empty map


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: creates an empty map")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val map = MiniMap.new()
check(map.is_empty())
check(map.len() == 0)
check(map.capacity == 4)
```

</details>

#### inserts and retrieves entries

- Verify: inserts and retrieves entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: inserts and retrieves entries")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var map = MiniMap.new()
map.insert("key", 42)
check(not map.is_empty())
check(map.len() == 1)
check(map.get("key") == Some(42))
check(map.has("key"))
```

</details>

#### updates an existing key without duplicating it

- Verify: updates an existing key without duplicating it


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: updates an existing key without duplicating it")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var map = MiniMap.new()
map.insert("key", 1)
map.insert("key", 2)
check(map.len() == 1)
check(map.get("key") == Some(2))
```

</details>

#### returns None for a missing key

- Verify: returns None for a missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: returns None for a missing key")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val map = MiniMap.new()
check(map.get("missing") == None)
check(not map.has("missing"))
```

</details>

#### removes entries and keeps other entries intact

- Verify: removes entries and keeps other entries intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: removes entries and keeps other entries intact")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var map = MiniMap.new()
map.insert("a", 1)
map.insert("b", 2)
map.insert("c", 3)

val removed = map.remove("b")
check(removed == Some(2))
check(map.len() == 2)
check(map.get("a") == Some(1))
check(map.get("b") == None)
check(map.get("c") == Some(3))
```

</details>

#### clears all entries

- Verify: clears all entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: clears all entries")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var map = MiniMap.new()
map.insert("a", 1)
map.insert("b", 2)
map.clear()

check(map.is_empty())
check(map.len() == 0)
check(map.get("a") == None)
check(sum_counts(map.buckets) == 0)
```

</details>

#### returns keys values and entries in insertion order

- Verify: returns keys values and entries in insertion order


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: returns keys values and entries in insertion order")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var map = MiniMap.new()
map.insert("a", 1)
map.insert("b", 2)

val keys = map.keys()
val values = map.values()
val entries = map.entries()

check(keys.len() == 2)
check_text(keys[0], "a")
check_text(keys[1], "b")
check(values.len() == 2)
check(values[0] == 1)
check(values[1] == 2)
check(entries.len() == 2)
check_text(entries[0].key, "a")
check(entries[0].value == 1)
check_text(entries[1].key, "b")
check(entries[1].value == 2)
```

</details>

#### grows capacity when the load threshold is exceeded

- Verify: grows capacity when the load threshold is exceeded


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: grows capacity when the load threshold is exceeded")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var map = MiniMap.with_capacity(4)
val initial_capacity = map.capacity
map.insert("a", 1)
map.insert("bb", 2)
map.insert("ccc", 3)
map.insert("dddd", 4)

check(map.capacity == initial_capacity * 2)
check(map.len() == 4)
check(map.get("a") == Some(1))
check(map.get("bb") == Some(2))
check(map.get("ccc") == Some(3))
check(map.get("dddd") == Some(4))
```

</details>

#### clones independently

- Verify: clones independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: clones independently")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var original = MiniMap.new()
original.insert("a", 1)
original.insert("b", 2)

val copy = original.clone()
original.insert("c", 3)

check(original.len() == 3)
check(copy.len() == 2)
check(copy.get("c") == None)
check(copy.get("a") == Some(1))
check(copy.get("b") == Some(2))
```

</details>

#### tracks bucket counts for inserted entries

- Verify: tracks bucket counts for inserted entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: tracks bucket counts for inserted entries")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var map = MiniMap.with_capacity(4)
map.insert("a", 1)
map.insert("bb", 2)
map.insert("ccc", 3)
map.insert("dddd", 4)

check(sum_counts(map.buckets) == 4)
check(map.buckets.len() == map.capacity)
check(map.capacity >= 4)
```

</details>

#### handles special and unicode keys

- Verify: handles special and unicode keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-MAP_MAP_CORRECTNESS-001
step("Verify: handles special and unicode keys")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var map = MiniMap.new()
map.insert("key\nwith\nnewlines", 1)
map.insert("key\twith\ttabs", 2)
map.insert("héllo", 3)

check(map.get("key\nwith\nnewlines") == Some(1))
check(map.get("key\twith\ttabs") == Some(2))
check(map.get("héllo") == Some(3))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `033f1cdf87a554518d9b34fe0fce5961a0dc73205cb52ed084d173675a461120`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `033f1cdf87a554518d9b34fe0fce5961a0dc73205cb52ed084d173675a461120`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `033f1cdf87a554518d9b34fe0fce5961a0dc73205cb52ed084d173675a461120`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/map/map_correctness_spec.spl
mirror: doc/06_spec/01_unit/std/map/map_correctness_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/map/map_correctness_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/map/map_correctness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/map/map_correctness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
