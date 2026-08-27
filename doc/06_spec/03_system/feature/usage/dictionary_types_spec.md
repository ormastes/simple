# Dictionary Types Specification

> Tests for dictionary (map) types and their operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dictionary Types Specification

Tests for dictionary (map) types and their operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1002 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/dictionary_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for dictionary (map) types and their operations.
Verifies dictionary creation, access, modification, and iteration.

## Scenarios

### Dictionary Types

#### dictionary creation

#### creates empty dictionary

- creates empty dictionary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates empty dictionary")
val empty: Dict<text, i32> = {}
expect empty.len() == 0
```

</details>

#### creates dictionary with initial values

- creates dictionary with initial values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates dictionary with initial values")
val dict = {"a": 1, "b": 2, "c": 3}
expect dict.len() == 3
```

</details>

#### creates dictionary with string keys and values

- creates dictionary with string keys and values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates dictionary with string keys and values")
val dict = {"name": "Alice", "city": "NYC"}
expect dict.len() == 2
```

</details>

#### dictionary access

#### retrieves value by key

- retrieves value by key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retrieves value by key")
val dict = {"a": 1, "b": 2}
expect dict["a"] == 1
```

</details>

#### returns null for missing key

- returns null for missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns null for missing key")
val dict = {"a": 1}
val value = dict.get("missing")
expect value == nil
```

</details>

#### checks key existence

- checks key existence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks key existence")
val dict = {"a": 1, "b": 2}
expect dict.contains("a") == true
expect dict.contains("c") == false
```

</details>

#### dictionary modification

#### adds new key-value pair

- adds new key-value pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds new key-value pair")
var dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
expect dict.len() == 2
```

</details>

#### updates existing value

- updates existing value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("updates existing value")
var dict = {"a": 1}
dict["a"] = 10
expect dict["a"] == 10
expect dict.len() == 1
```

</details>

#### removes entry by key

- removes entry by key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes entry by key")
var dict = {"a": 1, "b": 2}
dict.remove("a")
expect dict.contains("a") == false
expect dict.len() == 1
```

</details>

#### dictionary iteration

#### iterates over keys

- iterates over keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over keys")
val dict = {"a": 1, "b": 2, "c": 3}
var count = 0
for key in dict.keys():
    count = count + 1
expect count == 3
```

</details>

#### iterates over values

- iterates over values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over values")
val dict = {"a": 1, "b": 2, "c": 3}
var sum = 0
for value in dict.values():
    sum = sum + value
expect sum == 6
```

</details>

#### iterates over entries

- iterates over entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over entries")
val dict = {"a": 1, "b": 2}
var count = 0
for entry in dict:
    count = count + 1
expect count == 2
```

</details>

#### dictionary methods

#### gets dictionary size

- gets dictionary size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets dictionary size")
val dict = {"a": 1, "b": 2, "c": 3}
expect dict.len() == 3
```

</details>

#### checks if dictionary is empty

- checks if dictionary is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if dictionary is empty")
val empty: Dict<text, i32> = {}
val full = {"a": 1}
expect empty.is_empty() == true
expect full.is_empty() == false
```

</details>

#### clears dictionary

- clears dictionary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears dictionary")
var dict = {"a": 1, "b": 2}
dict.clear()
expect dict.len() == 0
expect dict.is_empty() == true
```

</details>

#### creates copy of dictionary

- creates copy of dictionary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates copy of dictionary")
val original = {"a": 1, "b": 2}
val copy = original.clone()
expect copy["a"] == 1
expect copy.len() == original.len()
```

</details>

#### dictionary with multiple types

#### stores different value types

- stores different value types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores different value types")
val mixed = {"int": 1, "text": "hello", "float": 3.14}
expect mixed.len() == 3
```

</details>

#### accesses values with correct types

- accesses values with correct types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses values with correct types")
val dict = {"count": 5}
val value = dict["count"]
expect value == 5
```

</details>

### Functional Dictionary Methods

#### set and merge

#### sets key with functional update

- sets key with functional update


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets key with functional update")
var d = {"a": 1}
d["b"] = 2
expect d["b"] == 2
```

</details>

#### merges two dictionaries

- merges two dictionaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("merges two dictionaries")
var d1 = {"a": 1}
val d2 = {"b": 2}
d1 = d1.merge(d2)
expect d1.len() == 2
```

</details>

#### get with default

#### gets value or default

- gets value or default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets value or default")
val d = {"a": 10}
expect d.get_or("b", 99) == 99
```

</details>

#### gets existing value instead of default

- gets existing value instead of default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets existing value instead of default")
val d = {"a": 10}
expect d.get_or("a", 99) == 10
```

</details>

### Dictionary Comprehension

#### creates dict from comprehension

- creates dict from comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates dict from comprehension")
val arr = [1, 2, 3]
val d = {x: x * x for x in arr}
expect d[2] == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b7cedccdb473d0021929def8c352119993296ef968eeef9f58f61a55a77c485`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b7cedccdb473d0021929def8c352119993296ef968eeef9f58f61a55a77c485`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b7cedccdb473d0021929def8c352119993296ef968eeef9f58f61a55a77c485`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/dictionary_types_spec.spl
mirror: doc/06_spec/03_system/feature/usage/dictionary_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/dictionary_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/dictionary_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/dictionary_types_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty dictionary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/dictionary_types_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates dictionary with initial values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/dictionary_types_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates dictionary with string keys and values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
