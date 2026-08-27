# Map Specification

> Tests covering Dict (Map).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Map Specification

## Scenarios

### Dict (Map)

#### Construction

#### creates empty dict

- creates empty dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates empty dict")
val m = {}
expect m.keys().len() == 0
```

</details>

#### Basic operations

#### inserts and retrieves value

- inserts and retrieves value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("inserts and retrieves value")
var m = {}
m["name"] = "Alice"
expect m["name"] == "Alice"
```

</details>

#### updates existing key

- updates existing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("updates existing key")
var m = {}
m["count"] = 1
m["count"] = 2
expect m["count"] == 2
```

</details>

#### contains_key returns true for existing keys

- contains_key returns true for existing keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("contains_key returns true for existing keys")
var m = {}
m["key"] = "value"
expect m.has("key")
```

</details>

#### contains_key returns false for missing keys

- contains_key returns false for missing keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("contains_key returns false for missing keys")
val m = {}
expect not m.has("missing")
```

</details>

#### len increases with insertions

- len increases with insertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("len increases with insertions")
var m = {}
expect m.keys().len() == 0
m["a"] = 1
expect m.keys().len() == 1
m["b"] = 2
expect m.keys().len() == 2
```

</details>

#### len does not increase for updates

- len does not increase for updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("len does not increase for updates")
var m = {}
m["key"] = 1
expect m.keys().len() == 1
m["key"] = 2
expect m.keys().len() == 1
```

</details>

#### Keys, values

#### keys returns all keys

- keys returns all keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("keys returns all keys")
var m = {}
m["a"] = 1
m["b"] = 2
m["c"] = 3
val keys = m.keys()
expect keys.len() == 3
```

</details>

#### empty dict returns empty key list

- empty dict returns empty key list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("empty dict returns empty key list")
val m = {}
expect m.keys().len() == 0
```

</details>

#### Multiple entries

#### handles many insertions

- handles many insertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("handles many insertions")
var m = {}
for i in 0..10:
    val k = "key{i}"
    m[k] = i
val klen = m.keys().len()
expect klen == 10
expect m["key5"] == 5
```

</details>

#### Different value types

#### stores integer values

- stores integer values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("stores integer values")
var m = {}
m["count"] = 42
expect m["count"] == 42
```

</details>

#### stores text values

- stores text values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("stores text values")
var m = {}
m["name"] = "Alice"
expect m["name"] == "Alice"
```

</details>

#### stores boolean values

- stores boolean values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("stores boolean values")
var m = {}
m["active"] = true
expect m["active"] == true
```

</details>

#### Edge cases

#### handles empty string key

- handles empty string key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("handles empty string key")
var m = {}
m[""] = "empty key"
expect m[""] == "empty key"
```

</details>

#### handles similar keys

- handles similar keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("handles similar keys")
var m = {}
m["test"] = 1
m["test1"] = 2
m["test2"] = 3
expect m["test"] == 1
expect m["test1"] == 2
```

</details>

#### Iteration

#### can iterate over entries

- can iterate over entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("can iterate over entries")
var m = {}
m["a"] = 1
m["b"] = 2
m["c"] = 3
var count = 0
for key in m.keys():
    count = count + 1
expect count == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/collections/map_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Dict (Map).
- Dict (Map)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f10dbc3fd7090a50d2ab601d359e7ead6d877e79191bbf87cde05a2795c1d826`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f10dbc3fd7090a50d2ab601d359e7ead6d877e79191bbf87cde05a2795c1d826`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f10dbc3fd7090a50d2ab601d359e7ead6d877e79191bbf87cde05a2795c1d826`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/shared/collections/map_spec.spl
mirror: doc/06_spec/shared/collections/map_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/collections/map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/collections/map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/collections/map_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/collections/map_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts and retrieves value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/collections/map_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates existing key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/collections/map_spec.spl:168:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can iterate over entries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
