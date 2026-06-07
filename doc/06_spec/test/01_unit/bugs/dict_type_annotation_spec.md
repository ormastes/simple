# Dict Type Annotation on Empty Dict Specification

> Verifies Dict behavior. The known bug INTERP-DICT-001 is that empty dict {} with type annotation is inferred as bool in interpreter mode. The tests below cover the safe workaround path instead of the broken empty annotation form.

<!-- sdn-diagram:id=dict_type_annotation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dict_type_annotation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dict_type_annotation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dict_type_annotation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Type Annotation on Empty Dict Specification

Verifies Dict behavior. The known bug INTERP-DICT-001 is that empty dict {} with type annotation is inferred as bool in interpreter mode. The tests below cover the safe workaround path instead of the broken empty annotation form.

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies Dict behavior. The known bug INTERP-DICT-001 is that empty
dict {} with type annotation is inferred as bool in interpreter mode.
The tests below cover the safe workaround path instead of the broken empty
annotation form.

## Workaround

Seed dicts with a dummy entry to force correct type inference.

## Scenarios

### Non-empty dict initialization

#### creates dict from literal with string keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"key": 42}
expect(d["key"]).to_equal(42)
```

</details>

#### creates dict with multiple entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"a": 1, "b": 2, "c": 3}
expect(d["a"]).to_equal(1)
expect(d["b"]).to_equal(2)
expect(d["c"]).to_equal(3)
```

</details>

#### allows adding entries to non-empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"init": 0}
d["new_key"] = 99
expect(d["new_key"]).to_equal(99)
```

</details>

#### allows overwriting entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"key": 1}
d["key"] = 2
expect(d["key"]).to_equal(2)
```

</details>

#### supports text values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"name": "Alice"}
expect(d["name"]).to_equal("Alice")
```

</details>

#### supports bool values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"active": true}
expect(d["active"]).to_equal(true)
```

</details>

### Dict workaround with seeded entry

#### seeded text-to-int dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"__init__": 0}
d["real_key"] = 42
expect(d["real_key"]).to_equal(42)
```

</details>

#### seeded text-to-text dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"__init__": ""}
d["name"] = "Bob"
expect(d["name"]).to_equal("Bob")
```

</details>

#### seeded text-to-bool dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"__init__": false}
d["flag"] = true
expect(d["flag"]).to_equal(true)
```

</details>

#### seeded dict with many insertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"x": 10}
d["y"] = 20
expect(d["x"]).to_equal(10)
expect(d["y"]).to_equal(20)
```

</details>

#### dict with numeric-like string keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"1": 100}
d["2"] = 200
d["3"] = 300
expect(d["1"]).to_equal(100)
expect(d["2"]).to_equal(200)
expect(d["3"]).to_equal(300)
```

</details>

#### dict with long string keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"short": 1}
d["a_very_long_key_name_here"] = 42
expect(d["a_very_long_key_name_here"]).to_equal(42)
```

</details>

#### dict with empty string key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"": 0}
d[""] = 99
expect(d[""]).to_equal(99)
```

</details>

#### dict with special char keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"name": "Alice"}
d["city"] = "NYC"
d["role"] = "Dev"
expect(d["name"]).to_equal("Alice")
expect(d["city"]).to_equal("NYC")
expect(d["role"]).to_equal("Dev")
```

</details>

#### overwrites text values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"key": "old"}
d["key"] = "new"
expect(d["key"]).to_equal("new")
```

</details>

#### stores empty string values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"key": "initial"}
d["empty"] = ""
expect(d["empty"]).to_equal("")
```

</details>

### Empty dict type annotation bug reproduction

#### seeded dict allows insertion after annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"__seed__": 0}
d["main"] = 42
expect(d["main"]).to_equal(42)
expect(d.len()).to_equal(2)
```

</details>

#### seeded dict allows multiple insertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"__seed__": 0}
expect(d.len()).to_equal(1)
d["value"] = 99
expect(d.len()).to_equal(2)
```

</details>

#### seeded dict behaves like typed empty dict workaround

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"__seed__": 0}
d["payload"] = 123
expect(d["payload"]).to_equal(123)
```

</details>

### Regression - collections still work

#### empty array with type annotation

1. items push
   - Expected: items[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var items: [i64] = []
items.push(42)
expect(items[0]).to_equal(42)
```

</details>

#### empty text array with type annotation

1. names push
   - Expected: names[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var names: [text] = []
names.push("hello")
expect(names[0]).to_equal("hello")
```

</details>

#### non-empty array works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect(nums.len()).to_equal(5)
expect(nums[0]).to_equal(1)
expect(nums[4]).to_equal(5)
```

</details>

#### nested array works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row_a = [1, 2]
val row_b = [3, 4]
val nested_rows = [row_a, row_b]
expect(nested_rows.len()).to_equal(2)
```

</details>

#### array push and access

1. arr push
2. arr push
3. arr push
   - Expected: arr.len() equals `3`
   - Expected: arr[0] equals `a`
   - Expected: arr[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = []
arr.push("a")
arr.push("b")
arr.push("c")
expect(arr.len()).to_equal(3)
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

- **Research:** [doc/bug/bug_report_dict_type_annotation_interpreter.md](doc/bug/bug_report_dict_type_annotation_interpreter.md)


</details>
