# Chained Enum Method Dispatch Regression Tests

> Tests for method calls on enum values. The chained `.unwrap().to_text()` pattern fails in the compiled runtime because the method dispatcher loses the concrete enum type after unwrap in a nested call context.

<!-- sdn-diagram:id=chained_enum_method_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chained_enum_method_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chained_enum_method_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chained_enum_method_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chained Enum Method Dispatch Regression Tests

Tests for method calls on enum values. The chained `.unwrap().to_text()` pattern fails in the compiled runtime because the method dispatcher loses the concrete enum type after unwrap in a nested call context.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime \| Testing |
| Status | Confirmed (runtime limitation) |
| Source | `test/01_unit/compiler/config/chained_enum_method_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for method calls on enum values. The chained `.unwrap().to_text()`
pattern fails in the compiled runtime because the method dispatcher loses
the concrete enum type after unwrap in a nested call context.

Workaround: use an intermediate variable to break the chain.

## Known Limitation

`TypeDefault.from_text("i32").unwrap().to_text()` — FAILS
`val td = TypeDefault.from_text("i32").unwrap(); td.to_text()` — WORKS

## Scenarios

### Enum Method After Unwrap (intermediate var)

#### TypeDefault from_text → unwrap → to_text

#### I32 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("i32").unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### I64 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("i64").unwrap()
expect(td.to_text()).to_equal("i64")
```

</details>

#### F32 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("f32").unwrap()
expect(td.to_text()).to_equal("f32")
```

</details>

#### F64 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("f64").unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### Bool via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("bool").unwrap()
expect(td.to_text()).to_equal("bool")
```

</details>

#### String via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("text").unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### Void via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("void").unwrap()
expect(td.to_text()).to_equal("void")
```

</details>

#### Any via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("any").unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

#### Nil via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("nil").unwrap()
expect(td.to_text()).to_equal("nil")
```

</details>

#### U8 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("u8").unwrap()
expect(td.to_text()).to_equal("u8")
```

</details>

#### U16 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("u16").unwrap()
expect(td.to_text()).to_equal("u16")
```

</details>

#### U32 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("u32").unwrap()
expect(td.to_text()).to_equal("u32")
```

</details>

#### U64 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("u64").unwrap()
expect(td.to_text()).to_equal("u64")
```

</details>

#### I8 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("i8").unwrap()
expect(td.to_text()).to_equal("i8")
```

</details>

#### I16 via intermediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("i16").unwrap()
expect(td.to_text()).to_equal("i16")
```

</details>

#### alias round-trips via intermediate

#### int alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("int").unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### long alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("long").unwrap()
expect(td.to_text()).to_equal("i64")
```

</details>

#### float alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("float").unwrap()
expect(td.to_text()).to_equal("f32")
```

</details>

#### double alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("double").unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### string alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("string").unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### byte alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("byte").unwrap()
expect(td.to_text()).to_equal("u8")
```

</details>

#### dynamic alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TypeDefault.from_text("dynamic").unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

### Direct Enum Method Chain (no unwrap)

#### CompilerProfile from_text().to_text()

#### Dev

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompilerProfile.from_text("dev").to_text()).to_equal("dev")
```

</details>

#### Prod

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompilerProfile.from_text("prod").to_text()).to_equal("prod")
```

</details>

#### Test

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompilerProfile.from_text("test").to_text()).to_equal("test")
```

</details>

#### Sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompilerProfile.from_text("sdn").to_text()).to_equal("sdn")
```

</details>

#### aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompilerProfile.from_text("production").to_text()).to_equal("prod")
expect(CompilerProfile.from_text("development").to_text()).to_equal("dev")
expect(CompilerProfile.from_text("testing").to_text()).to_equal("test")
expect(CompilerProfile.from_text("release").to_text()).to_equal("prod")
expect(CompilerProfile.from_text("data").to_text()).to_equal("sdn")
```

</details>

#### enum method on struct field

#### TypeInferenceConfig field chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.default()
expect(config.empty_array_default.to_text()).to_equal("i32")
expect(config.empty_vector_default.to_text()).to_equal("f64")
expect(config.empty_dict_key_default.to_text()).to_equal("text")
expect(config.empty_dict_value_default.to_text()).to_equal("any")
```

</details>

#### from_sdn result field chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.from_sdn("empty_array, i64").unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

### Result Unwrap + Struct Field

#### from_sdn result unwrap

#### unwrap Ok then access field method

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "empty_array, f32\nempty_vector, i64"
val config = TypeInferenceConfig.from_sdn(sdn).unwrap()
expect(config.empty_array_default.to_text()).to_equal("f32")
expect(config.empty_vector_default.to_text()).to_equal("i64")
```

</details>

#### unwrap Ok and check strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TypeInferenceConfig.from_sdn("strict, true").unwrap()
expect(config.strict_empty_collections).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
