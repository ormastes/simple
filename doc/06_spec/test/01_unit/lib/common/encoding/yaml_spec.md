# Yaml Specification

> <details>

<!-- sdn-diagram:id=yaml_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=yaml_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

yaml_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=yaml_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Yaml Specification

## Scenarios

### YAML parse — simple key-value mapping

#### parses two key-value pairs into two entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_kv_count()).to_equal(2)
```

</details>

#### gets value for key 'name'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_kv_name()).to_equal("Alice")
```

</details>

#### gets value for key 'age'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_kv_age()).to_equal("30")
```

</details>

#### returns empty string for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_kv_missing()).to_equal("")
```

</details>

### YAML parse — integer and boolean values

#### parses integer value as text '42'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_int_value()).to_equal("42")
```

</details>

#### parses boolean true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_bool_true()).to_equal("true")
```

</details>

#### parses boolean false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_bool_false()).to_equal("false")
```

</details>

### YAML parse — sequence (list items with -)

#### parses three sequence items

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_seq_count()).to_equal(3)
```

</details>

#### first sequence item is 'apple'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_seq_first()).to_equal("apple")
```

</details>

#### yaml_get_list retrieves two items from a sequence value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_seq_under_key_count()).to_equal(2)
```

</details>

### YAML parse — nested mapping

#### nested mapping produces one top-level entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_nested_count()).to_equal(1)
```

</details>

#### nested mapping has key 'server'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_nested_key_exists()).to_equal(true)
```

</details>

### YAML parse — flow sequence [a, b, c]

#### flow sequence has three items

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_flow_seq_count()).to_equal(3)
```

</details>

#### first item of flow sequence is 'alpha'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_flow_seq_first()).to_equal("alpha")
```

</details>

### YAML parse — flow mapping {k: v}

#### flow mapping has two pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_flow_map_count()).to_equal(2)
```

</details>

#### get 'name' from flow mapping returns 'Bob'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_flow_map_get()).to_equal("Bob")
```

</details>

### YAML parse — comments ignored

#### comment line does not produce an entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_comment_count()).to_equal(1)
```

</details>

#### value after comment is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_comment_value()).to_equal("hello")
```

</details>

### YAML parse — quoted strings

#### double-quoted string with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_double_quoted()).to_equal("hello world")
```

</details>

#### single-quoted string with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_single_quoted()).to_equal("foo bar")
```

</details>

### YAML encode — round-trip for simple mappings

#### encodes two pairs as YAML lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encode_simple_round_trip()).to_equal("name: Alice\nage: 30")
```

</details>

### YAML encode — scalar quoting

#### plain scalar needs no quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encode_scalar_plain()).to_equal("hello")
```

</details>

#### scalar with colon gets quoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encode_scalar_with_colon()).to_equal("\"key: value\"")
```

</details>

#### boolean keyword gets quoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encode_scalar_bool()).to_equal("\"true\"")
```

</details>

#### empty string gets quoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encode_scalar_empty()).to_equal("\"\"")
```

</details>

### YAML get by key

#### get existing key returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_get_by_key_found()).to_equal("Tokyo")
```

</details>

#### get missing key returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_get_by_key_missing_empty()).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/yaml_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- YAML parse — simple key-value mapping
- YAML parse — integer and boolean values
- YAML parse — sequence (list items with -)
- YAML parse — nested mapping
- YAML parse — flow sequence [a, b, c]
- YAML parse — flow mapping {k: v}
- YAML parse — comments ignored
- YAML parse — quoted strings
- YAML encode — round-trip for simple mappings
- YAML encode — scalar quoting
- YAML get by key

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
