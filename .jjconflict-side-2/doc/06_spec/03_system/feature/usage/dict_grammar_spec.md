# Dictionary Grammar and Syntax Specification

> Tests for dictionary literal syntax, ensuring correct grammar is used.

<!-- sdn-diagram:id=dict_grammar_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dict_grammar_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dict_grammar_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dict_grammar_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dictionary Grammar and Syntax Specification

Tests for dictionary literal syntax, ensuring correct grammar is used.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1002, #1018 |
| Category | Language, Syntax |
| Status | Complete |
| Source | `test/03_system/feature/usage/dict_grammar_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for dictionary literal syntax, ensuring correct grammar is used.
Verifies that {"key": value} syntax works correctly.

## Scenarios

### Dictionary Grammar

#### basic dict syntax

#### creates dict with string keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = {"name": "Alice", "age": 30}
expect config["name"] == "Alice"
expect config["age"] == 30
```

</details>

#### creates dict with integer values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scores = {"math": 95, "science": 87, "history": 92}
expect scores["math"] == 95
```

</details>

#### creates dict with mixed value types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"count": 42, "name": "test", "active": true}
expect data["count"] == 42
expect data["active"] == true
```

</details>

#### creates nested dicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = {"outer": {"inner": 123}}
expect nested["outer"]["inner"] == 123
```

</details>

#### creates empty dict

1. expect empty len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: Dict<text, i32> = {}
expect empty.len() == 0
```

</details>

#### dict with arrays

#### stores arrays as values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"numbers": [1, 2, 3], "letters": ["a", "b", "c"]}
expect data["numbers"][0] == 1
expect data["letters"][2] == "c"
```

</details>

#### stores nested structures

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val complex = {
    "users": [
        {"name": "Alice", "id": 1},
        {"name": "Bob", "id": 2}
    ]
}
expect complex["users"][0]["name"] == "Alice"
```

</details>

#### dict operations

#### inserts new key-value pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
```

</details>

#### updates existing value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"x": 10}
dict["x"] = 20
expect dict["x"] == 20
```

</details>

#### checks key existence

1. expect dict has
2. expect not dict has


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"key": "value"}
expect dict.has("key")
expect not dict.has("missing")
```

</details>

#### gets keys

1. expect keys len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2, "c": 3}
val keys = dict.keys()
expect keys.len() == 3
```

</details>

#### gets values

1. expect values len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2}
val values = dict.values()
expect values.len() == 2
```

</details>

#### dict with optional chaining

#### stores optional values

1. expect dict["present"] == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"present": Some(42), "absent": nil}
expect dict["present"] == Some(42)
```

</details>

#### uses optional chaining with dict access

1. expect dict["key"]? to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"key": Some("value")}
expect dict["key"]?.to_string() == Some("value")
```

</details>

#### returns nil for missing key with ?

1. expect dict get


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1}
expect dict.get("missing") == nil
```

</details>

#### dict type annotations

#### annotates string to int dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict: Dict<text, i32> = {"one": 1, "two": 2}
expect dict["one"] == 1
```

</details>

#### annotates string to string dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict: Dict<text, text> = {"greeting": "hello"}
expect dict["greeting"] == "hello"
```

</details>

#### annotates complex value types

1. expect dict["nums"] len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict: Dict<text, [i32]> = {"nums": [1, 2, 3]}
expect dict["nums"].len() == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
