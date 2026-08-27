# Freeze and Unfreeze Collections for Immutability

> The `freeze()` function converts mutable collections (arrays and dicts) into immutable snapshots that support read operations but prevent modification. Frozen collections retain full access to non-mutating operations like indexing, iteration, `map`, `filter`, `reduce`, `keys`, `values`, and `contains`. This spec validates freeze behavior on arrays and dicts, confirms idempotence (freezing an already-frozen collection is a no-op), and verifies that functional operations produce correct results on frozen data.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Freeze and Unfreeze Collections for Immutability

The `freeze()` function converts mutable collections (arrays and dicts) into immutable snapshots that support read operations but prevent modification. Frozen collections retain full access to non-mutating operations like indexing, iteration, `map`, `filter`, `reduce`, `keys`, `values`, and `contains`. This spec validates freeze behavior on arrays and dicts, confirms idempotence (freezing an already-frozen collection is a no-op), and verifies that functional operations produce correct results on frozen data.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-025 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/freeze_unfreeze_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `freeze()` function converts mutable collections (arrays and dicts) into immutable
snapshots that support read operations but prevent modification. Frozen collections
retain full access to non-mutating operations like indexing, iteration, `map`, `filter`,
`reduce`, `keys`, `values`, and `contains`. This spec validates freeze behavior on arrays
and dicts, confirms idempotence (freezing an already-frozen collection is a no-op),
and verifies that functional operations produce correct results on frozen data.

## Syntax

```simple
var arr = [1, 2, 3]
use std.spec.step

val frozen = freeze(arr)           # immutable snapshot
frozen.map(_1 * 2)                # [2, 4, 6] - functional ops work
frozen.filter(_1 % 2 == 0)        # filtering works on frozen

var dict = {"a": 1, "b": 2}
val frozen_dict = freeze(dict)     # frozen dict
frozen_dict.keys()                 # read-only access to keys
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `freeze()` | Converts a mutable collection into an immutable copy |
| Idempotence | Calling `freeze()` on an already-frozen collection returns an equivalent value |
| Read-only access | Frozen collections support indexing, `len`, `first`, `last`, negative indexing |
| Functional operations | `map`, `filter`, `reduce`, `contains` all work on frozen collections |
| Dict freeze | Frozen dicts support `keys`, `values`, `contains_key`, and key-based access |

## Scenarios

### Freeze and Unfreeze

#### Freeze Function

#### freezes mutable array

- freezes mutable array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("freezes mutable array")
var arr = [1, 2, 3]
val frozen = freeze(arr)
expect frozen[0] == 1
expect frozen.len() == 3
```

</details>

#### freezes mutable dict

- freezes mutable dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("freezes mutable dict")
var dict = {"a": 1}
val frozen = freeze(dict)
expect frozen["a"] == 1
```

</details>

#### is idempotent

- is idempotent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is idempotent")
val arr = freeze([1, 2, 3])
val frozen_again = freeze(arr)
expect frozen_again[0] == arr[0]
expect frozen_again.len() == arr.len()
```

</details>

#### freezes empty array

- freezes empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("freezes empty array")
val frozen = freeze([])
expect frozen.len() == 0
```

</details>

#### freezes empty dict

- freezes empty dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("freezes empty dict")
val frozen = freeze({})
expect frozen.len() == 0
```

</details>

#### Frozen Array Operations

#### allows reads on frozen array

- allows reads on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows reads on frozen array")
val frozen = freeze([1, 2, 3])
expect frozen[0] == 1
expect frozen[2] == 3
```

</details>

#### allows len on frozen array

- allows len on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows len on frozen array")
val frozen = freeze([1, 2, 3])
expect frozen.len() == 3
```

</details>

#### allows iteration on frozen array

- allows iteration on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows iteration on frozen array")
val frozen = freeze([1, 2, 3])
var sum = 0
for x in frozen:
    sum = sum + x
expect sum == 6
```

</details>

#### allows first and last on frozen array

- allows first and last on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows first and last on frozen array")
val frozen = freeze([1, 2, 3])
expect frozen.first() == 1
expect frozen.last() == 3
```

</details>

#### allows negative indexing on frozen array

- allows negative indexing on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows negative indexing on frozen array")
val frozen = freeze([1, 2, 3])
expect frozen[-1] == 3
expect frozen[-2] == 2
```

</details>

#### Functional Operations on Frozen

#### allows map on frozen array

- allows map on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows map on frozen array")
val frozen = freeze([1, 2, 3])
val doubled = frozen.map(_1 * 2)
expect doubled[0] == 2
expect doubled[1] == 4
expect doubled[2] == 6
```

</details>

#### allows filter on frozen array

- allows filter on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows filter on frozen array")
val frozen = freeze([1, 2, 3, 4, 5])
val evens = frozen.filter(_1 % 2 == 0)
expect evens[0] == 2
expect evens.len() == 2
expect evens[1] == 4
```

</details>

#### allows reduce on frozen array

- allows reduce on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows reduce on frozen array")
val frozen = freeze([1, 2, 3, 4])
val sum = frozen.reduce(0, \acc, x: acc + x)
expect sum == 10
```

</details>

#### allows contains on frozen array

- allows contains on frozen array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows contains on frozen array")
val frozen = freeze([1, 2, 3])
expect frozen.contains(2)
expect not frozen.contains(5)
```

</details>

#### Frozen Dict Operations

#### allows reads on frozen dict

- allows reads on frozen dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows reads on frozen dict")
val frozen = freeze({"a": 1, "b": 2})
expect frozen["a"] == 1
expect frozen["b"] == 2
```

</details>

#### allows len on frozen dict

- allows len on frozen dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows len on frozen dict")
val frozen = freeze({"a": 1, "b": 2})
expect frozen.len() == 2
```

</details>

#### allows keys on frozen dict

- allows keys on frozen dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows keys on frozen dict")
val frozen = freeze({"a": 1, "b": 2})
val keys = frozen.keys()
expect keys.len() == 2
```

</details>

#### allows values on frozen dict

- allows values on frozen dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows values on frozen dict")
val frozen = freeze({"a": 1, "b": 2})
val values = frozen.values()
expect values.len() == 2
```

</details>

#### allows contains_key on frozen dict

- allows contains_key on frozen dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows contains_key on frozen dict")
val frozen = freeze({"a": 1})
expect frozen.has("a")
expect not frozen.has("b")
```

</details>

#### Type Behavior

#### treats frozen arrays as arrays

- treats frozen arrays as arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats frozen arrays as arrays")
val frozen = freeze([1, 2, 3])
expect frozen[0] == 1
expect frozen.len() == 3
```

</details>

#### treats frozen dicts as dicts

- treats frozen dicts as dicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats frozen dicts as dicts")
val frozen = freeze({"a": 1})
expect frozen["a"] == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `8f2aefad9959380334eed6c9917229ce94d1eb83fc83eb9ab942b89933240c0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f2aefad9959380334eed6c9917229ce94d1eb83fc83eb9ab942b89933240c0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f2aefad9959380334eed6c9917229ce94d1eb83fc83eb9ab942b89933240c0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/freeze_unfreeze_spec.spl
mirror: doc/06_spec/03_system/feature/usage/freeze_unfreeze_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/freeze_unfreeze_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/freeze_unfreeze_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/freeze_unfreeze_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'freezes mutable array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/freeze_unfreeze_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'freezes mutable dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/freeze_unfreeze_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is idempotent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
