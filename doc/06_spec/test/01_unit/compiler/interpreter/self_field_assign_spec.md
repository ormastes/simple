# Self Field Assign Specification

> 1. var counter = MutableCounter

<!-- sdn-diagram:id=self_field_assign_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=self_field_assign_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

self_field_assign_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=self_field_assign_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Self Field Assign Specification

## Scenarios

### interpreter self field assignment

#### allows self.field assignment inside me methods

1. var counter = MutableCounter
2. counter set value
   - Expected: counter.value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = MutableCounter(value: 1)
counter.set_value(7)
expect(counter.value).to_equal(7)
```

</details>

#### allows self.field[index] assignment inside me methods

1. var holder = MutableListHolder
2. holder set first
   - Expected: holder.values[0] equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var holder = MutableListHolder(values: [1, 2])
holder.set_first(9)
expect(holder.values[0]).to_equal(9)
```

</details>

#### preserves self.field mutations passed through free functions

1. var holder = MutableListHolder
2. holder set first via free function
   - Expected: holder.values[0] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var holder = MutableListHolder(values: [1, 2])
holder.set_first_via_free_function(11)
expect(holder.values[0]).to_equal(11)
```

</details>

#### preserves self receiver mutations passed through free functions

1. var holder = MutableListHolder
2. holder set first via self free function
   - Expected: holder.values[0] equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var holder = MutableListHolder(values: [1, 2])
holder.set_first_via_self_free_function(13)
expect(holder.values[0]).to_equal(13)
```

</details>

#### preserves mutations through free functions whose parameter is named self

1. var holder = MutableListHolder
2. write holder named self
   - Expected: holder.values[0] equals `17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var holder = MutableListHolder(values: [1, 2])
write_holder_named_self(holder, 17)
expect(holder.values[0]).to_equal(17)
```

</details>

#### preserves dictionary-field mutations through free functions

1. var holder = MutableDictHolder
2. write dict holder
   - Expected: holder.values.has("answer") is true
   - Expected: holder.values["answer"] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var holder = MutableDictHolder(values: {})
write_dict_holder(holder, "answer", 42)
expect(holder.values.has("answer")).to_equal(true)
expect(holder.values["answer"]).to_equal(42)
```

</details>

#### preserves struct dictionary-field mutations through returning free functions

1. var holder = MutableStructDictHolder
   - Expected: holder.values.has("answer") is true
   - Expected: "unexpected" equals `success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var holder = MutableStructDictHolder(values: {})
val result = write_struct_dict_holder(holder, "answer", 43)
match result:
    case DictWriteResult.Success:
        expect(holder.values.has("answer")).to_equal(true)
    case _:
        expect("unexpected").to_equal("success")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/self_field_assign_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- interpreter self field assignment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
