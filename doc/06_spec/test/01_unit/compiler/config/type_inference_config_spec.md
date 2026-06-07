# TypeInferenceConfig & TypeDefault Specification

> Tests for TypeDefault enum and TypeInferenceConfig struct — pure logic type inference configuration that works in interpreter mode.

<!-- sdn-diagram:id=type_inference_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_inference_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_inference_config_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_inference_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 63 | 63 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TypeInferenceConfig & TypeDefault Specification

Tests for TypeDefault enum and TypeInferenceConfig struct — pure logic type inference configuration that works in interpreter mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/01_unit/compiler/config/type_inference_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for TypeDefault enum and TypeInferenceConfig struct — pure logic
type inference configuration that works in interpreter mode.

## Scenarios

### TypeDefault

#### to_text

#### converts Void

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.Void.to_text()).to_equal("void")
```

</details>

#### converts Bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.Bool.to_text()).to_equal("bool")
```

</details>

#### converts I8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.I8.to_text()).to_equal("i8")
```

</details>

#### converts I16

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.I16.to_text()).to_equal("i16")
```

</details>

#### converts I32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.I32.to_text()).to_equal("i32")
```

</details>

#### converts I64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.I64.to_text()).to_equal("i64")
```

</details>

#### converts U8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.U8.to_text()).to_equal("u8")
```

</details>

#### converts U16

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.U16.to_text()).to_equal("u16")
```

</details>

#### converts U32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.U32.to_text()).to_equal("u32")
```

</details>

#### converts U64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.U64.to_text()).to_equal("u64")
```

</details>

#### converts F32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.F32.to_text()).to_equal("f32")
```

</details>

#### converts F64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.F64.to_text()).to_equal("f64")
```

</details>

#### converts String

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.String.to_text()).to_equal("text")
```

</details>

#### converts Nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.Nil.to_text()).to_equal("nil")
```

</details>

#### converts Any

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TypeDefault.Any.to_text()).to_equal("any")
```

</details>

#### from_text

#### parses i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("i32")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### parses int alias to I32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("int")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### parses i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("i64")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("i64")
```

</details>

#### parses long alias to I64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("long")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("i64")
```

</details>

#### parses f32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("f32")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("f32")
```

</details>

#### parses float alias to F32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("float")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("f32")
```

</details>

#### parses f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("f64")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### parses double alias to F64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("double")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### parses text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("text")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### parses string alias to String

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("string")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### parses str alias to String

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("str")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### parses bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("bool")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("bool")
```

</details>

#### parses void

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("void")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("void")
```

</details>

#### parses unit alias to Void

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("unit")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("void")
```

</details>

#### parses u8

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("u8")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("u8")
```

</details>

#### parses byte alias to U8

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("byte")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("u8")
```

</details>

#### parses any

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("any")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

#### parses dynamic alias to Any

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("dynamic")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

#### parses nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("nil")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("nil")
```

</details>

#### parses null alias to Nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("null")
expect(result.?).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("nil")
```

</details>

#### returns nil for invalid input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("garbage")
expect(result.?).to_equal(false)
```

</details>

#### returns nil for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TypeDefault.from_text("")
expect(result.?).to_equal(false)
```

</details>

#### round-trip

#### I32 round-trips through text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = TypeDefault.I32
val text_form = original.to_text()
val restored = TypeDefault.from_text(text_form)
expect(restored.?).to_equal(true)
val td = restored.unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### F64 round-trips through text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = TypeDefault.F64
val text_form = original.to_text()
val restored = TypeDefault.from_text(text_form)
expect(restored.?).to_equal(true)
val td = restored.unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### Any round-trips through text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = TypeDefault.Any
val text_form = original.to_text()
val restored = TypeDefault.from_text(text_form)
expect(restored.?).to_equal(true)
val td = restored.unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

### TypeInferenceConfig

#### default

#### has I32 for empty array default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.default()
expect(config.empty_array_default.to_text()).to_equal("i32")
```

</details>

#### has F64 for empty vector default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.default()
expect(config.empty_vector_default.to_text()).to_equal("f64")
```

</details>

#### has String for empty dict key default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.default()
expect(config.empty_dict_key_default.to_text()).to_equal("text")
```

</details>

#### has Any for empty dict value default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.default()
expect(config.empty_dict_value_default.to_text()).to_equal("any")
```

</details>

#### is not strict by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.default()
expect(config.strict_empty_collections).to_equal(false)
```

</details>

#### strict

#### creates strict config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.strict()
expect(config.strict_empty_collections).to_equal(true)
```

</details>

#### strict config has same type defaults as default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.strict()
expect(config.empty_array_default.to_text()).to_equal("i32")
expect(config.empty_vector_default.to_text()).to_equal("f64")
```

</details>

#### with_strict

#### creates non-strict when false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.with_strict(false)
expect(config.strict_empty_collections).to_equal(false)
```

</details>

#### creates strict when true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.with_strict(true)
expect(config.strict_empty_collections).to_equal(true)
```

</details>

#### from_sdn

#### parses empty array default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "empty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### parses empty vector default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "empty_vector, f32"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_vector_default.to_text()).to_equal("f32")
```

</details>

#### parses empty dict key default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "empty_dict_key, i32"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_dict_key_default.to_text()).to_equal("i32")
```

</details>

#### parses empty dict value default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "empty_dict_value, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_dict_value_default.to_text()).to_equal("i64")
```

</details>

#### parses strict mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "strict, true"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.strict_empty_collections).to_equal(true)
```

</details>

#### parses multiple fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "empty_array, i64\nempty_vector, f32\nstrict, true"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
expect(config.empty_vector_default.to_text()).to_equal("f32")
expect(config.strict_empty_collections).to_equal(true)
```

</details>

#### skips comments and empty lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "# comment\n\nempty_array, i64\n# another comment"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### skips header lines starting with pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "| key | value |\nempty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### skips type_inference header line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "type_inference\nempty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### ignores unknown keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "unknown_key, some_value\nempty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### keeps defaults for unparsed fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "empty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
# Only array was overridden; others keep defaults
expect(config.empty_vector_default.to_text()).to_equal("f64")
expect(config.empty_dict_key_default.to_text()).to_equal("text")
```

</details>

#### accepts alternate key names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "empty_array_default, i64\nempty_vector_default, f32"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
expect(config.empty_vector_default.to_text()).to_equal("f32")
```

</details>

#### merge

#### returns module config

1. var module = TypeInferenceConfig with strict
   - Expected: merged.strict_empty_collections is true
   - Expected: merged.empty_array_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val project = TypeInferenceConfig.default()
var module = TypeInferenceConfig.with_strict(true)
module.empty_array_default = TypeDefault.I64
val merged = project.merge(module)
expect(merged.strict_empty_collections).to_equal(true)
expect(merged.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### module config fully overrides project config

1. var project = TypeInferenceConfig default
   - Expected: merged.empty_array_default.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var project = TypeInferenceConfig.default()
project.empty_array_default = TypeDefault.F64
val module = TypeInferenceConfig.default()
val merged = project.merge(module)
# Module default (I32) takes precedence over project (F64)
expect(merged.empty_array_default.to_text()).to_equal("i32")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 63 |
| Active scenarios | 63 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
