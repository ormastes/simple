# Sql Codec Specification

> <details>

<!-- sdn-diagram:id=sql_codec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_codec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_codec_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_codec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Codec Specification

## Scenarios

### DbCodec

#### table_name

#### returns the table name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codec = TestUserCodec()
expect(codec.table_name()).to_equal("test_users")
```

</details>

#### schema

#### returns a TableSchema with correct columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codec = TestUserCodec()
val schema = codec.schema()
expect(schema.name).to_equal("test_users")
val names = schema.column_names()
expect(names.len()).to_equal(3)
expect(names[0]).to_equal("id")
expect(names[1]).to_equal("name")
expect(names[2]).to_equal("age")
```

</details>

#### columns

#### returns insert column names without id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codec = TestUserCodec()
val cols = codec.columns()
expect(cols.len()).to_equal(2)
expect(cols[0]).to_equal("name")
expect(cols[1]).to_equal("age")
```

</details>

#### encode

#### encodes entity to DbValue array

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codec = TestUserCodec()
val user = TestUser(name: "Alice", age: 30)
val values = codec.encode(user)
expect(values.len()).to_equal(2)
val name_val = values[0].as_text()
expect(name_val.?).to_equal(true)
expect(name_val?).to_equal("Alice")
val age_val = values[1].as_int()
expect(age_val.?).to_equal(true)
expect(age_val?).to_equal(30)
```

</details>

#### encodes different entities correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codec = TestUserCodec()
val user = TestUser(name: "Bob", age: 25)
val values = codec.encode(user)
expect(values[0].as_text()?).to_equal("Bob")
expect(values[1].as_int()?).to_equal(25)
```

</details>

#### decode

#### decodes DbRow to entity

1. values: [DbValue Integer
   - Expected: user.name equals `Alice`
   - Expected: user.age equals `30`
   - Expected: "decode should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codec = TestUserCodec()
val row = DbRow(
    columns: ["id", "name", "age"],
    values: [DbValue.Integer(value: 1), DbValue.Text(value: "Alice"), DbValue.Integer(value: 30)]
)
val result = codec.decode(row)
if val Ok(user) = result:
    expect(user.name).to_equal("Alice")
    expect(user.age).to_equal(30)
else:
    expect("decode should succeed").to_equal("")
```

</details>

#### returns error for missing columns

1. values: [DbValue Integer
   - Expected: "decode should fail for missing columns" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codec = TestUserCodec()
val row = DbRow(
    columns: ["id"],
    values: [DbValue.Integer(value: 1)]
)
val result = codec.decode(row)
if val Err(e) = result:
    expect(e.message()).to_contain("mismatch")
else:
    expect("decode should fail for missing columns").to_equal("")
```

</details>

#### round-trip

#### encode then decode produces same values

1. values: [DbValue Integer
   - Expected: decoded.name equals `original.name`
   - Expected: decoded.age equals `original.age`
   - Expected: "round-trip should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codec = TestUserCodec()
val original = TestUser(name: "Charlie", age: 42)
val encoded = codec.encode(original)

# Simulate what a DB row would look like
val row = DbRow(
    columns: ["id", "name", "age"],
    values: [DbValue.Integer(value: 1), encoded[0], encoded[1]]
)
val result = codec.decode(row)
if val Ok(decoded) = result:
    expect(decoded.name).to_equal(original.name)
    expect(decoded.age).to_equal(original.age)
else:
    expect("round-trip should succeed").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/sql/sql_codec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DbCodec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
