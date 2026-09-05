# Persistent Dict Intensive Specification

> Tests covering PersistentDict, Core operations, Immutability, Bulk operations, Conversion, Edge cases, Array helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Dict Intensive Specification

## Scenarios

### PersistentDict

### Core operations

#### creates an empty dict

- creates an empty dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an empty dict")
val dict = PersistentDict.new()
assert dict.len() == 0
assert dict.is_empty()
```

</details>

#### inserts and retrieves a value

- inserts and retrieves a value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts and retrieves a value")
val dict = PersistentDict.new().set("key", 42)
assert dict.len() == 1
assert dict.get("key") == Some(42)
```

</details>

#### updates an existing key

- updates an existing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates an existing key")
val dict1 = PersistentDict.new().set("key", 1)
val dict2 = dict1.set("key", 2)
assert dict1.get("key") == Some(1)
assert dict2.get("key") == Some(2)
```

</details>

#### removes a key

- removes a key


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a key")
val dict1 = PersistentDict.new().set("a", 1).set("b", 2)
val dict2 = dict1.remove("a")
assert dict1.len() == 2
assert dict2.len() == 1
assert dict2.get("a") == None
assert dict2.get("b") == Some(2)
```

</details>

### Immutability

#### keeps earlier versions unchanged

- keeps earlier versions unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps earlier versions unchanged")
val base = PersistentDict.new().set("a", 1)
val next = base.set("b", 2)
val final = next.remove("a")
assert base.get("b") == None
assert next.get("a") == Some(1)
assert final.get("a") == None
```

</details>

#### supports a small version chain

- supports a small version chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports a small version chain")
var versions: [PersistentDict] = []
var dict = PersistentDict.new()
for i in 0..25:
    versions = versions + [dict]
    dict = dict.set("key_{i}", i)

assert versions[0].len() == 0
assert versions[10].len() == 10
assert dict.len() == 25
```

</details>

### Bulk operations

#### merge combines dicts

- merge combines dicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merge combines dicts")
val dict1 = PersistentDict.new().set("a", 1).set("b", 2)
val dict2 = PersistentDict.new().set("b", 20).set("c", 3)
val merged = dict1.merge(dict2)
assert merged.len() == 3
assert merged.get("a") == Some(1)
assert merged.get("b") == Some(20)
assert merged.get("c") == Some(3)
```

</details>

#### filter keeps matching entries

- filter keeps matching entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filter keeps matching entries")
var dict = PersistentDict.new()
for i in 0..12:
    dict = dict.set("key_{i}", i)

val evens = dict.filter(\k, v: v % 2 == 0)
assert evens.len() == 6
assert evens.get("key_0") == Some(0)
assert evens.get("key_1") == None
assert evens.get("key_10") == Some(10)
```

</details>

#### map_values transforms values

- map_values transforms values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("map_values transforms values")
val doubled = PersistentDict.new()
    .set("a", 1)
    .set("b", 2)
    .map_values(_1 * 2)
assert doubled.get("a") == Some(2)
assert doubled.get("b") == Some(4)
```

</details>

### Conversion

#### round-trips through entries

- round-trips through entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips through entries")
val dict = PersistentDict.from_entries([
    ("a", 1),
    ("b", 2),
    ("c", 3)
])
val entries = dict.entries()
assert dict.len() == 3
assert entries.len() == 3
assert entries_has(entries, "a", 1)
assert entries_has(entries, "b", 2)
assert entries_has(entries, "c", 3)
```

</details>

#### returns keys and values

- returns keys and values


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns keys and values")
val dict = PersistentDict.from_entries([
    ("a", 1),
    ("b", 2)
])
val keys = dict.keys()
val values = dict.values()
assert keys.len() == 2
assert values.len() == 2
assert keys.contains("a")
assert keys.contains("b")
assert values.contains(1)
assert values.contains(2)
```

</details>

### Edge cases

#### handles empty string keys

- handles empty string keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string keys")
val dict = PersistentDict.new().set("", 42)
assert dict.get("") == Some(42)
```

</details>

#### handles unicode keys

- handles unicode keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unicode keys")
val dict = PersistentDict.new()
    .set("héllo", 1)
    .set("世界", 2)
    .set("🚀", 3)
assert dict.get("héllo") == Some(1)
assert dict.get("世界") == Some(2)
assert dict.get("🚀") == Some(3)
```

</details>

### Array helpers

#### inserts, updates, and removes at the expected position

- inserts, updates, and removes at the expected position


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts, updates, and removes at the expected position")
val arr = [1, 2, 3]
assert array_insert(arr, 1, 99) == [1, 99, 2, 3]
assert array_update(arr, 1, 99) == [1, 99, 3]
assert array_remove(arr, 1) == [1, 3]
```

</details>

#### leaves the original array unchanged

- leaves the original array unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the original array unchanged")
val arr = [1, 2, 3]
val _ = array_insert(arr, 1, 99)
val _ = array_update(arr, 1, 99)
val _ = array_remove(arr, 1)
assert arr == [1, 2, 3]
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/interpreter/collections/persistent_dict_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PersistentDict, Core operations, Immutability, Bulk operations, Conversion, Edge cases, Array helpers.
- PersistentDict
- Core operations
- Immutability
- Bulk operations
- Conversion
- Edge cases
- Array helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `1a33a212e2d920f73feedfb4cef8ad3f9f4e6f3903846549ffba4ef9d8005cb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a33a212e2d920f73feedfb4cef8ad3f9f4e6f3903846549ffba4ef9d8005cb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a33a212e2d920f73feedfb4cef8ad3f9f4e6f3903846549ffba4ef9d8005cb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/interpreter/collections/persistent_dict_intensive_spec.spl
mirror: doc/06_spec/unit/app/interpreter/collections/persistent_dict_intensive_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/interpreter/collections/persistent_dict_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/interpreter/collections/persistent_dict_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/interpreter/collections/persistent_dict_intensive_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an empty dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/interpreter/collections/persistent_dict_intensive_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts and retrieves a value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/interpreter/collections/persistent_dict_intensive_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates an existing key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
