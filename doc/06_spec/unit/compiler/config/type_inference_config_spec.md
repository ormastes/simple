# TypeInferenceConfig & TypeDefault Specification

> Tests for TypeDefault enum and TypeInferenceConfig struct — pure logic type inference configuration that works in interpreter mode.

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
| Source | `test/unit/compiler/config/type_inference_config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for TypeDefault enum and TypeInferenceConfig struct — pure logic
type inference configuration that works in interpreter mode.

## Scenarios

### TypeDefault

#### to_text

#### converts Void

- converts Void
   - Expected: TypeDefault.Void.to_text() equals `void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Void")
expect(TypeDefault.Void.to_text()).to_equal("void")
```

</details>

#### converts Bool

- converts Bool
   - Expected: TypeDefault.Bool.to_text() equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Bool")
expect(TypeDefault.Bool.to_text()).to_equal("bool")
```

</details>

#### converts I8

- converts I8
   - Expected: TypeDefault.I8.to_text() equals `i8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts I8")
expect(TypeDefault.I8.to_text()).to_equal("i8")
```

</details>

#### converts I16

- converts I16
   - Expected: TypeDefault.I16.to_text() equals `i16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts I16")
expect(TypeDefault.I16.to_text()).to_equal("i16")
```

</details>

#### converts I32

- converts I32
   - Expected: TypeDefault.I32.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts I32")
expect(TypeDefault.I32.to_text()).to_equal("i32")
```

</details>

#### converts I64

- converts I64
   - Expected: TypeDefault.I64.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts I64")
expect(TypeDefault.I64.to_text()).to_equal("i64")
```

</details>

#### converts U8

- converts U8
   - Expected: TypeDefault.U8.to_text() equals `u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts U8")
expect(TypeDefault.U8.to_text()).to_equal("u8")
```

</details>

#### converts U16

- converts U16
   - Expected: TypeDefault.U16.to_text() equals `u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts U16")
expect(TypeDefault.U16.to_text()).to_equal("u16")
```

</details>

#### converts U32

- converts U32
   - Expected: TypeDefault.U32.to_text() equals `u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts U32")
expect(TypeDefault.U32.to_text()).to_equal("u32")
```

</details>

#### converts U64

- converts U64
   - Expected: TypeDefault.U64.to_text() equals `u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts U64")
expect(TypeDefault.U64.to_text()).to_equal("u64")
```

</details>

#### converts F32

- converts F32
   - Expected: TypeDefault.F32.to_text() equals `f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts F32")
expect(TypeDefault.F32.to_text()).to_equal("f32")
```

</details>

#### converts F64

- converts F64
   - Expected: TypeDefault.F64.to_text() equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts F64")
expect(TypeDefault.F64.to_text()).to_equal("f64")
```

</details>

#### converts String

- converts String
   - Expected: TypeDefault.String.to_text() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts String")
expect(TypeDefault.String.to_text()).to_equal("text")
```

</details>

#### converts Nil

- converts Nil
   - Expected: TypeDefault.Nil.to_text() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Nil")
expect(TypeDefault.Nil.to_text()).to_equal("nil")
```

</details>

#### converts Any

- converts Any
   - Expected: TypeDefault.Any.to_text() equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Any")
expect(TypeDefault.Any.to_text()).to_equal("any")
```

</details>

#### from_text

#### parses i32

- parses i32
   - Expected: result != nil is true
   - Expected: td.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses i32")
val result = TypeDefault.from_text("i32")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### parses int alias to I32

- parses int alias to I32
   - Expected: result != nil is true
   - Expected: td.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses int alias to I32")
val result = TypeDefault.from_text("int")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### parses i64

- parses i64
   - Expected: result != nil is true
   - Expected: td.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses i64")
val result = TypeDefault.from_text("i64")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("i64")
```

</details>

#### parses long alias to I64

- parses long alias to I64
   - Expected: result != nil is true
   - Expected: td.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses long alias to I64")
val result = TypeDefault.from_text("long")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("i64")
```

</details>

#### parses f32

- parses f32
   - Expected: result != nil is true
   - Expected: td.to_text() equals `f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses f32")
val result = TypeDefault.from_text("f32")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("f32")
```

</details>

#### parses float alias to F32

- parses float alias to F32
   - Expected: result != nil is true
   - Expected: td.to_text() equals `f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses float alias to F32")
val result = TypeDefault.from_text("float")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("f32")
```

</details>

#### parses f64

- parses f64
   - Expected: result != nil is true
   - Expected: td.to_text() equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses f64")
val result = TypeDefault.from_text("f64")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### parses double alias to F64

- parses double alias to F64
   - Expected: result != nil is true
   - Expected: td.to_text() equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses double alias to F64")
val result = TypeDefault.from_text("double")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### parses text

- parses text
   - Expected: result != nil is true
   - Expected: td.to_text() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses text")
val result = TypeDefault.from_text("text")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### parses string alias to String

- parses string alias to String
   - Expected: result != nil is true
   - Expected: td.to_text() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses string alias to String")
val result = TypeDefault.from_text("string")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### parses str alias to String

- parses str alias to String
   - Expected: result != nil is true
   - Expected: td.to_text() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses str alias to String")
val result = TypeDefault.from_text("str")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### parses bool

- parses bool
   - Expected: result != nil is true
   - Expected: td.to_text() equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bool")
val result = TypeDefault.from_text("bool")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("bool")
```

</details>

#### parses void

- parses void
   - Expected: result != nil is true
   - Expected: td.to_text() equals `void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses void")
val result = TypeDefault.from_text("void")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("void")
```

</details>

#### parses unit alias to Void

- parses unit alias to Void
   - Expected: result != nil is true
   - Expected: td.to_text() equals `void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses unit alias to Void")
val result = TypeDefault.from_text("unit")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("void")
```

</details>

#### parses u8

- parses u8
   - Expected: result != nil is true
   - Expected: td.to_text() equals `u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses u8")
val result = TypeDefault.from_text("u8")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("u8")
```

</details>

#### parses byte alias to U8

- parses byte alias to U8
   - Expected: result != nil is true
   - Expected: td.to_text() equals `u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses byte alias to U8")
val result = TypeDefault.from_text("byte")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("u8")
```

</details>

#### parses any

- parses any
   - Expected: result != nil is true
   - Expected: td.to_text() equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses any")
val result = TypeDefault.from_text("any")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

#### parses dynamic alias to Any

- parses dynamic alias to Any
   - Expected: result != nil is true
   - Expected: td.to_text() equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses dynamic alias to Any")
val result = TypeDefault.from_text("dynamic")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

#### parses nil

- parses nil
   - Expected: result != nil is true
   - Expected: td.to_text() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nil")
val result = TypeDefault.from_text("nil")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("nil")
```

</details>

#### parses null alias to Nil

- parses null alias to Nil
   - Expected: result != nil is true
   - Expected: td.to_text() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses null alias to Nil")
val result = TypeDefault.from_text("null")
expect(result != nil).to_equal(true)
val td = result.unwrap()
expect(td.to_text()).to_equal("nil")
```

</details>

#### returns nil for invalid input

- returns nil for invalid input
   - Expected: result != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for invalid input")
val result = TypeDefault.from_text("garbage")
expect(result != nil).to_equal(false)
```

</details>

#### returns nil for empty string

- returns nil for empty string
   - Expected: result != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty string")
val result = TypeDefault.from_text("")
expect(result != nil).to_equal(false)
```

</details>

#### round-trip

#### I32 round-trips through text

- I32 round-trips through text
   - Expected: restored != nil is true
   - Expected: td.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("I32 round-trips through text")
val original = TypeDefault.I32
val text_form = original.to_text()
val restored = TypeDefault.from_text(text_form)
expect(restored != nil).to_equal(true)
val td = restored.unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### F64 round-trips through text

- F64 round-trips through text
   - Expected: restored != nil is true
   - Expected: td.to_text() equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F64 round-trips through text")
val original = TypeDefault.F64
val text_form = original.to_text()
val restored = TypeDefault.from_text(text_form)
expect(restored != nil).to_equal(true)
val td = restored.unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### Any round-trips through text

- Any round-trips through text
   - Expected: restored != nil is true
   - Expected: td.to_text() equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Any round-trips through text")
val original = TypeDefault.Any
val text_form = original.to_text()
val restored = TypeDefault.from_text(text_form)
expect(restored != nil).to_equal(true)
val td = restored.unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

### TypeInferenceConfig

#### default

#### has I32 for empty array default

- has I32 for empty array default
   - Expected: config.empty_array_default.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has I32 for empty array default")
val config = TypeInferenceConfig.default()
expect(config.empty_array_default.to_text()).to_equal("i32")
```

</details>

#### has F64 for empty vector default

- has F64 for empty vector default
   - Expected: config.empty_vector_default.to_text() equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has F64 for empty vector default")
val config = TypeInferenceConfig.default()
expect(config.empty_vector_default.to_text()).to_equal("f64")
```

</details>

#### has String for empty dict key default

- has String for empty dict key default
   - Expected: config.empty_dict_key_default.to_text() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has String for empty dict key default")
val config = TypeInferenceConfig.default()
expect(config.empty_dict_key_default.to_text()).to_equal("text")
```

</details>

#### has Any for empty dict value default

- has Any for empty dict value default
   - Expected: config.empty_dict_value_default.to_text() equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Any for empty dict value default")
val config = TypeInferenceConfig.default()
expect(config.empty_dict_value_default.to_text()).to_equal("any")
```

</details>

#### is not strict by default

- is not strict by default
   - Expected: config.strict_empty_collections is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not strict by default")
val config = TypeInferenceConfig.default()
expect(config.strict_empty_collections).to_equal(false)
```

</details>

#### strict

#### creates strict config

- creates strict config
   - Expected: config.strict_empty_collections is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates strict config")
val config = TypeInferenceConfig.strict()
expect(config.strict_empty_collections).to_equal(true)
```

</details>

#### strict config has same type defaults as default

- strict config has same type defaults as default
   - Expected: config.empty_array_default.to_text() equals `i32`
   - Expected: config.empty_vector_default.to_text() equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strict config has same type defaults as default")
val config = TypeInferenceConfig.strict()
expect(config.empty_array_default.to_text()).to_equal("i32")
expect(config.empty_vector_default.to_text()).to_equal("f64")
```

</details>

#### with_strict

#### creates non-strict when false

- creates non-strict when false
   - Expected: config.strict_empty_collections is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates non-strict when false")
val config = TypeInferenceConfig.with_strict(false)
expect(config.strict_empty_collections).to_equal(false)
```

</details>

#### creates strict when true

- creates strict when true
   - Expected: config.strict_empty_collections is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates strict when true")
val config = TypeInferenceConfig.with_strict(true)
expect(config.strict_empty_collections).to_equal(true)
```

</details>

#### from_sdn

#### parses empty array default

- parses empty array default
   - Expected: config.empty_array_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty array default")
val sdn = "empty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### parses empty vector default

- parses empty vector default
   - Expected: config.empty_vector_default.to_text() equals `f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty vector default")
val sdn = "empty_vector, f32"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_vector_default.to_text()).to_equal("f32")
```

</details>

#### parses empty dict key default

- parses empty dict key default
   - Expected: config.empty_dict_key_default.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty dict key default")
val sdn = "empty_dict_key, i32"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_dict_key_default.to_text()).to_equal("i32")
```

</details>

#### parses empty dict value default

- parses empty dict value default
   - Expected: config.empty_dict_value_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty dict value default")
val sdn = "empty_dict_value, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_dict_value_default.to_text()).to_equal("i64")
```

</details>

#### parses strict mode

- parses strict mode
   - Expected: config.strict_empty_collections is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses strict mode")
val sdn = "strict, true"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.strict_empty_collections).to_equal(true)
```

</details>

#### parses multiple fields

- parses multiple fields
   - Expected: config.empty_array_default.to_text() equals `i64`
   - Expected: config.empty_vector_default.to_text() equals `f32`
   - Expected: config.strict_empty_collections is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple fields")
val sdn = "empty_array, i64\nempty_vector, f32\nstrict, true"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
expect(config.empty_vector_default.to_text()).to_equal("f32")
expect(config.strict_empty_collections).to_equal(true)
```

</details>

#### skips comments and empty lines

- skips comments and empty lines
   - Expected: config.empty_array_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips comments and empty lines")
val sdn = "# comment\n\nempty_array, i64\n# another comment"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### skips header lines starting with pipe

- skips header lines starting with pipe
   - Expected: config.empty_array_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips header lines starting with pipe")
val sdn = "| key | value |\nempty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### skips type_inference header line

- skips type_inference header line
   - Expected: config.empty_array_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips type_inference header line")
val sdn = "type_inference\nempty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### ignores unknown keys

- ignores unknown keys
   - Expected: config.empty_array_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores unknown keys")
val sdn = "unknown_key, some_value\nempty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### keeps defaults for unparsed fields

- keeps defaults for unparsed fields
   - Expected: config.empty_vector_default.to_text() equals `f64`
   - Expected: config.empty_dict_key_default.to_text() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps defaults for unparsed fields")
val sdn = "empty_array, i64"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
# Only array was overridden; others keep defaults
expect(config.empty_vector_default.to_text()).to_equal("f64")
expect(config.empty_dict_key_default.to_text()).to_equal("text")
```

</details>

#### accepts alternate key names

- accepts alternate key names
   - Expected: config.empty_array_default.to_text() equals `i64`
   - Expected: config.empty_vector_default.to_text() equals `f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts alternate key names")
val sdn = "empty_array_default, i64\nempty_vector_default, f32"
val result = TypeInferenceConfig.from_sdn(sdn)
val config = result.unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
expect(config.empty_vector_default.to_text()).to_equal("f32")
```

</details>

#### merge

#### returns module config

- returns module config
   - Expected: merged.strict_empty_collections is true
   - Expected: merged.empty_array_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns module config")
val project = TypeInferenceConfig.default()
var module = TypeInferenceConfig.with_strict(true)
module.empty_array_default = TypeDefault.I64
val merged = project.merge(module)
expect(merged.strict_empty_collections).to_equal(true)
expect(merged.empty_array_default.to_text()).to_equal("i64")
```

</details>

#### module config fully overrides project config

- module config fully overrides project config
   - Expected: merged.empty_array_default.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module config fully overrides project config")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e16f5f3e5cb7e23f842fc032a8fac130f115f4da2608fd84cae62300aab55b03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e16f5f3e5cb7e23f842fc032a8fac130f115f4da2608fd84cae62300aab55b03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e16f5f3e5cb7e23f842fc032a8fac130f115f4da2608fd84cae62300aab55b03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/config/type_inference_config_spec.spl
mirror: doc/06_spec/unit/compiler/config/type_inference_config_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/config/type_inference_config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/config/type_inference_config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/config/type_inference_config_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Void' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/config/type_inference_config_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/config/type_inference_config_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts I8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
