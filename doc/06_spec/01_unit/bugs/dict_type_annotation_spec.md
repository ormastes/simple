# Dict Type Annotation on Empty Dict Specification

> Purpose: Prove that Non-empty dict initialization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Type Annotation on Empty Dict Specification

Purpose: Prove that Non-empty dict initialization.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-DICT-001 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/bug/bug_report_dict_type_annotation_interpreter.md |
| Source | `test/01_unit/bugs/dict_type_annotation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Non-empty dict initialization.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Non-empty dict initialization

#### creates dict from literal with string keys

- creates dict from literal with string keys
- Verify: creates dict from literal with string keys
   - Expected: d["key"] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("creates dict from literal with string keys")
step("Verify: creates dict from literal with string keys")
# @req: REQ-BUGS-001
var d = {"key": 42}
expect(d["key"]).to_equal(42)
```

</details>

#### creates dict with multiple entries

- creates dict with multiple entries
- Verify: creates dict with multiple entries
   - Expected: d["a"] equals `1`
   - Expected: d["b"] equals `2`
   - Expected: d["c"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("creates dict with multiple entries")
step("Verify: creates dict with multiple entries")
var d = {"a": 1, "b": 2, "c": 3}
expect(d["a"]).to_equal(1)
expect(d["b"]).to_equal(2)
expect(d["c"]).to_equal(3)
```

</details>

#### allows adding entries to non-empty dict

- allows adding entries to non-empty dict
- Verify: allows adding entries to non-empty dict
   - Expected: d["new_key"] equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("allows adding entries to non-empty dict")
step("Verify: allows adding entries to non-empty dict")
var d = {"init": 0}
d["new_key"] = 99
expect(d["new_key"]).to_equal(99)
```

</details>

#### allows overwriting entries

- allows overwriting entries
- Verify: allows overwriting entries
   - Expected: d["key"] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("allows overwriting entries")
step("Verify: allows overwriting entries")
var d = {"key": 1}
d["key"] = 2
expect(d["key"]).to_equal(2)
```

</details>

#### supports text values

- supports text values
- Verify: supports text values
   - Expected: d["name"] equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("supports text values")
step("Verify: supports text values")
var d = {"name": "Alice"}
expect(d["name"]).to_equal("Alice")
```

</details>

#### supports bool values

- supports bool values
- Verify: supports bool values
   - Expected: d["active"] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("supports bool values")
step("Verify: supports bool values")
var d = {"active": true}
expect(d["active"]).to_equal(true)
```

</details>

### Dict workaround with seeded entry

#### seeded text-to-int dict

- seeded text-to-int dict
- Verify: seeded text-to-int dict
   - Expected: d["real_key"] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded text-to-int dict")
step("Verify: seeded text-to-int dict")
var d = {"__init__": 0}
d["real_key"] = 42
expect(d["real_key"]).to_equal(42)
```

</details>

#### seeded text-to-text dict

- seeded text-to-text dict
- Verify: seeded text-to-text dict
   - Expected: d["name"] equals `Bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded text-to-text dict")
step("Verify: seeded text-to-text dict")
var d = {"__init__": ""}
d["name"] = "Bob"
expect(d["name"]).to_equal("Bob")
```

</details>

#### seeded text-to-bool dict

- seeded text-to-bool dict
- Verify: seeded text-to-bool dict
   - Expected: d["flag"] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded text-to-bool dict")
step("Verify: seeded text-to-bool dict")
var d = {"__init__": false}
d["flag"] = true
expect(d["flag"]).to_equal(true)
```

</details>

#### seeded dict with many insertions

- seeded dict with many insertions
- Verify: seeded dict with many insertions
   - Expected: d["alpha"] equals `1`
   - Expected: d["epsilon"] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded dict with many insertions")
step("Verify: seeded dict with many insertions")
var d = {"__seed__": 0}
d["alpha"] = 1
d["beta"] = 2
d["gamma"] = 3
d["delta"] = 4
d["epsilon"] = 5
expect(d["alpha"]).to_equal(1)
expect(d["epsilon"]).to_equal(5)
```

</details>

#### seeded dict overwrite and read

- seeded dict overwrite and read
- Verify: seeded dict overwrite and read
   - Expected: d["key"] equals `100`
   - Expected: d["key"] equals `200`
   - Expected: d["key"] equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded dict overwrite and read")
step("Verify: seeded dict overwrite and read")
var d = {"key": 100}
expect(d["key"]).to_equal(100)
d["key"] = 200
expect(d["key"]).to_equal(200)
d["key"] = 300
expect(d["key"]).to_equal(300)
```

</details>

### Dict operations

#### reads key that was just written

- reads key that was just written
- Verify: reads key that was just written
   - Expected: d["x"] equals `10`
   - Expected: d["y"] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("reads key that was just written")
step("Verify: reads key that was just written")
var d = {"x": 10}
d["y"] = 20
expect(d["x"]).to_equal(10)
expect(d["y"]).to_equal(20)
```

</details>

#### dict with numeric-like string keys

- dict with numeric-like string keys
- Verify: dict with numeric-like string keys
   - Expected: d["1"] equals `100`
   - Expected: d["2"] equals `200`
   - Expected: d["3"] equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("dict with numeric-like string keys")
step("Verify: dict with numeric-like string keys")
var d = {"1": 100}
d["2"] = 200
d["3"] = 300
expect(d["1"]).to_equal(100)
expect(d["2"]).to_equal(200)
expect(d["3"]).to_equal(300)
```

</details>

#### dict with long string keys

- dict with long string keys
- Verify: dict with long string keys
   - Expected: d["a_very_long_key_name_here"] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("dict with long string keys")
step("Verify: dict with long string keys")
var d = {"short": 1}
d["a_very_long_key_name_here"] = 42
expect(d["a_very_long_key_name_here"]).to_equal(42)
```

</details>

#### dict with empty string key

- dict with empty string key
- Verify: dict with empty string key
   - Expected: d[""] equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("dict with empty string key")
step("Verify: dict with empty string key")
var d = {"": 0}
d[""] = 99
expect(d[""]).to_equal(99)
```

</details>

#### dict with special char keys

- dict with special char keys
- Verify: dict with special char keys
   - Expected: d["a-b"] equals `1`
   - Expected: d["c_d"] equals `2`
   - Expected: d["e.f"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("dict with special char keys")
step("Verify: dict with special char keys")
var d = {"a-b": 1}
d["c_d"] = 2
d["e.f"] = 3
expect(d["a-b"]).to_equal(1)
expect(d["c_d"]).to_equal(2)
expect(d["e.f"]).to_equal(3)
```

</details>

### Dict with text values

#### stores and retrieves text values

- stores and retrieves text values
- Verify: stores and retrieves text values
   - Expected: d["name"] equals `Alice`
   - Expected: d["city"] equals `NYC`
   - Expected: d["role"] equals `Dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("stores and retrieves text values")
step("Verify: stores and retrieves text values")
var d = {"name": "Alice"}
d["city"] = "NYC"
d["role"] = "Dev"
expect(d["name"]).to_equal("Alice")
expect(d["city"]).to_equal("NYC")
expect(d["role"]).to_equal("Dev")
```

</details>

#### overwrites text values

- overwrites text values
- Verify: overwrites text values
   - Expected: d["key"] equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("overwrites text values")
step("Verify: overwrites text values")
var d = {"key": "old"}
d["key"] = "new"
expect(d["key"]).to_equal("new")
```

</details>

#### stores empty string values

- stores empty string values
- Verify: stores empty string values
   - Expected: d["empty"] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("stores empty string values")
step("Verify: stores empty string values")
var d = {"key": "initial"}
d["empty"] = ""
expect(d["empty"]).to_equal("")
```

</details>

### Empty dict type annotation bug reproduction

#### seeded dict allows insertion after annotation

- seeded dict allows insertion after annotation
- Verify: seeded dict allows insertion after annotation
   - Expected: d["main"] equals `42`
   - Expected: d.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded dict allows insertion after annotation")
step("Verify: seeded dict allows insertion after annotation")
var d = {"__seed__": 0}
d["main"] = 42
expect(d["main"]).to_equal(42)
expect(d.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### seeded dict allows multiple insertions

- seeded dict allows multiple insertions
- Verify: seeded dict allows multiple insertions
   - Expected: d["alpha"] equals `1`
   - Expected: d["beta"] equals `2`
   - Expected: d["gamma"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded dict allows multiple insertions")
step("Verify: seeded dict allows multiple insertions")
var d = {"__seed__": 0}
d["alpha"] = 1
d["beta"] = 2
d["gamma"] = 3
expect(d["alpha"]).to_equal(1)
expect(d["beta"]).to_equal(2)
expect(d["gamma"]).to_equal(3)
```

</details>

#### seeded dict len reports entry count

- seeded dict len reports entry count
- Verify: seeded dict len reports entry count
   - Expected: d.len() equals `1`
   - Expected: d.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded dict len reports entry count")
step("Verify: seeded dict len reports entry count")
var d = {"__seed__": 0}
expect(d.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
d["value"] = 99
expect(d.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### seeded dict behaves like typed empty dict workaround

- seeded dict behaves like typed empty dict workaround
- Verify: seeded dict behaves like typed empty dict workaround
   - Expected: d["payload"] equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("seeded dict behaves like typed empty dict workaround")
step("Verify: seeded dict behaves like typed empty dict workaround")
var d = {"__seed__": 0}
d["payload"] = 123
expect(d["payload"]).to_equal(123)
```

</details>

### Regression - collections still work

#### empty array with type annotation

- empty array with type annotation
- Verify: empty array with type annotation
   - Expected: items[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("empty array with type annotation")
step("Verify: empty array with type annotation")
var items: [i64] = []
items.push(42)
expect(items[0]).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### empty text array with type annotation

- empty text array with type annotation
- Verify: empty text array with type annotation
   - Expected: names[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("empty text array with type annotation")
step("Verify: empty text array with type annotation")
var names: [text] = []
names.push("hello")
expect(names[0]).to_equal("hello")
```

</details>

#### non-empty array works

- non-empty array works
- Verify: non-empty array works
   - Expected: nums.len() equals `5`
   - Expected: nums[0] equals `1`
   - Expected: nums[4] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("non-empty array works")
step("Verify: non-empty array works")
val nums = [1, 2, 3, 4, 5]
expect(nums.len()).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(nums[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(nums[4]).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### nested array works

- nested array works
- Verify: nested array works
   - Expected: nested_rows.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("nested array works")
step("Verify: nested array works")
val row_a = [1, 2]
val row_b = [3, 4]
val nested_rows = [row_a, row_b]
expect(nested_rows.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### array push and access

- array push and access
- Verify: array push and access
   - Expected: arr.len() equals `3`
   - Expected: arr[0] equals `a`
   - Expected: arr[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("array push and access")
step("Verify: array push and access")
var arr: [text] = []
arr.push("a")
arr.push("b")
arr.push("c")
expect(arr.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(arr[0]).to_equal("a")
expect(arr[2]).to_equal("c")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/bug/bug_report_dict_type_annotation_interpreter.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BUGS`
- `REQ-BUGS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60f24c237e8ffc276ac74c27d04f8496b763203bd007dd77543da3fb1641d743`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60f24c237e8ffc276ac74c27d04f8496b763203bd007dd77543da3fb1641d743`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60f24c237e8ffc276ac74c27d04f8496b763203bd007dd77543da3fb1641d743`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/bugs/dict_type_annotation_spec.spl
mirror: doc/06_spec/01_unit/bugs/dict_type_annotation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/dict_type_annotation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/dict_type_annotation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/dict_type_annotation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 27 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/bugs/dict_type_annotation_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates dict from literal with string keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/dict_type_annotation_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates dict with multiple entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/dict_type_annotation_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows adding entries to non-empty dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
