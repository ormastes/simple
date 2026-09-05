# Chained Enum Method Dispatch Regression Tests

> Tests for method calls on enum values. The chained `.unwrap().to_text()` pattern fails in the compiled runtime because the method dispatcher loses the concrete enum type after unwrap in a nested call context.

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
| Updated | 2026-08-26 |
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

- I32 via intermediate
   - Expected: td.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("I32 via intermediate")
val td = TypeDefault.from_text("i32").unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### I64 via intermediate

- I64 via intermediate
   - Expected: td.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("I64 via intermediate")
val td = TypeDefault.from_text("i64").unwrap()
expect(td.to_text()).to_equal("i64")
```

</details>

#### F32 via intermediate

- F32 via intermediate
   - Expected: td.to_text() equals `f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("F32 via intermediate")
val td = TypeDefault.from_text("f32").unwrap()
expect(td.to_text()).to_equal("f32")
```

</details>

#### F64 via intermediate

- F64 via intermediate
   - Expected: td.to_text() equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("F64 via intermediate")
val td = TypeDefault.from_text("f64").unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### Bool via intermediate

- Bool via intermediate
   - Expected: td.to_text() equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Bool via intermediate")
val td = TypeDefault.from_text("bool").unwrap()
expect(td.to_text()).to_equal("bool")
```

</details>

#### String via intermediate

- String via intermediate
   - Expected: td.to_text() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("String via intermediate")
val td = TypeDefault.from_text("text").unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### Void via intermediate

- Void via intermediate
   - Expected: td.to_text() equals `void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Void via intermediate")
val td = TypeDefault.from_text("void").unwrap()
expect(td.to_text()).to_equal("void")
```

</details>

#### Any via intermediate

- Any via intermediate
   - Expected: td.to_text() equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Any via intermediate")
val td = TypeDefault.from_text("any").unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

#### Nil via intermediate

- Nil via intermediate
   - Expected: td.to_text() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Nil via intermediate")
val td = TypeDefault.from_text("nil").unwrap()
expect(td.to_text()).to_equal("nil")
```

</details>

#### U8 via intermediate

- U8 via intermediate
   - Expected: td.to_text() equals `u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("U8 via intermediate")
val td = TypeDefault.from_text("u8").unwrap()
expect(td.to_text()).to_equal("u8")
```

</details>

#### U16 via intermediate

- U16 via intermediate
   - Expected: td.to_text() equals `u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("U16 via intermediate")
val td = TypeDefault.from_text("u16").unwrap()
expect(td.to_text()).to_equal("u16")
```

</details>

#### U32 via intermediate

- U32 via intermediate
   - Expected: td.to_text() equals `u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("U32 via intermediate")
val td = TypeDefault.from_text("u32").unwrap()
expect(td.to_text()).to_equal("u32")
```

</details>

#### U64 via intermediate

- U64 via intermediate
   - Expected: td.to_text() equals `u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("U64 via intermediate")
val td = TypeDefault.from_text("u64").unwrap()
expect(td.to_text()).to_equal("u64")
```

</details>

#### I8 via intermediate

- I8 via intermediate
   - Expected: td.to_text() equals `i8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("I8 via intermediate")
val td = TypeDefault.from_text("i8").unwrap()
expect(td.to_text()).to_equal("i8")
```

</details>

#### I16 via intermediate

- I16 via intermediate
   - Expected: td.to_text() equals `i16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("I16 via intermediate")
val td = TypeDefault.from_text("i16").unwrap()
expect(td.to_text()).to_equal("i16")
```

</details>

#### alias round-trips via intermediate

#### int alias

- int alias
   - Expected: td.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("int alias")
val td = TypeDefault.from_text("int").unwrap()
expect(td.to_text()).to_equal("i32")
```

</details>

#### long alias

- long alias
   - Expected: td.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("long alias")
val td = TypeDefault.from_text("long").unwrap()
expect(td.to_text()).to_equal("i64")
```

</details>

#### float alias

- float alias
   - Expected: td.to_text() equals `f32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("float alias")
val td = TypeDefault.from_text("float").unwrap()
expect(td.to_text()).to_equal("f32")
```

</details>

#### double alias

- double alias
   - Expected: td.to_text() equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("double alias")
val td = TypeDefault.from_text("double").unwrap()
expect(td.to_text()).to_equal("f64")
```

</details>

#### string alias

- string alias
   - Expected: td.to_text() equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("string alias")
val td = TypeDefault.from_text("string").unwrap()
expect(td.to_text()).to_equal("text")
```

</details>

#### byte alias

- byte alias
   - Expected: td.to_text() equals `u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("byte alias")
val td = TypeDefault.from_text("byte").unwrap()
expect(td.to_text()).to_equal("u8")
```

</details>

#### dynamic alias

- dynamic alias
   - Expected: td.to_text() equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dynamic alias")
val td = TypeDefault.from_text("dynamic").unwrap()
expect(td.to_text()).to_equal("any")
```

</details>

### Direct Enum Method Chain (no unwrap)

#### CompilerProfile from_text().to_text()

#### Dev

- Dev
   - Expected: CompilerProfile.from_text("dev").to_text() equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Dev")
expect(CompilerProfile.from_text("dev").to_text()).to_equal("dev")
```

</details>

#### Prod

- Prod
   - Expected: CompilerProfile.from_text("prod").to_text() equals `prod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Prod")
expect(CompilerProfile.from_text("prod").to_text()).to_equal("prod")
```

</details>

#### Test

- Test
   - Expected: CompilerProfile.from_text("test").to_text() equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Test")
expect(CompilerProfile.from_text("test").to_text()).to_equal("test")
```

</details>

#### Sdn

- Sdn
   - Expected: CompilerProfile.from_text("sdn").to_text() equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Sdn")
expect(CompilerProfile.from_text("sdn").to_text()).to_equal("sdn")
```

</details>

#### aliases

- aliases
   - Expected: CompilerProfile.from_text("production").to_text() equals `prod`
   - Expected: CompilerProfile.from_text("development").to_text() equals `dev`
   - Expected: CompilerProfile.from_text("testing").to_text() equals `test`
   - Expected: CompilerProfile.from_text("release").to_text() equals `prod`
   - Expected: CompilerProfile.from_text("data").to_text() equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("aliases")
expect(CompilerProfile.from_text("production").to_text()).to_equal("prod")
expect(CompilerProfile.from_text("development").to_text()).to_equal("dev")
expect(CompilerProfile.from_text("testing").to_text()).to_equal("test")
expect(CompilerProfile.from_text("release").to_text()).to_equal("prod")
expect(CompilerProfile.from_text("data").to_text()).to_equal("sdn")
```

</details>

#### enum method on struct field

#### TypeInferenceConfig field chain

- TypeInferenceConfig field chain
   - Expected: config.empty_array_default.to_text() equals `i32`
   - Expected: config.empty_vector_default.to_text() equals `f64`
   - Expected: config.empty_dict_key_default.to_text() equals `text`
   - Expected: config.empty_dict_value_default.to_text() equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TypeInferenceConfig field chain")
val config = TypeInferenceConfig.default()
expect(config.empty_array_default.to_text()).to_equal("i32")
expect(config.empty_vector_default.to_text()).to_equal("f64")
expect(config.empty_dict_key_default.to_text()).to_equal("text")
expect(config.empty_dict_value_default.to_text()).to_equal("any")
```

</details>

#### from_sdn result field chain

- from_sdn result field chain
   - Expected: config.empty_array_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("from_sdn result field chain")
val config = TypeInferenceConfig.from_sdn("empty_array, i64").unwrap()
expect(config.empty_array_default.to_text()).to_equal("i64")
```

</details>

### Result Unwrap + Struct Field

#### from_sdn result unwrap

#### unwrap Ok then access field method

- unwrap Ok then access field method
   - Expected: config.empty_array_default.to_text() equals `f32`
   - Expected: config.empty_vector_default.to_text() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwrap Ok then access field method")
val sdn = "empty_array, f32\nempty_vector, i64"
val config = TypeInferenceConfig.from_sdn(sdn).unwrap()
expect(config.empty_array_default.to_text()).to_equal("f32")
expect(config.empty_vector_default.to_text()).to_equal("i64")
```

</details>

#### unwrap Ok and check strict

- unwrap Ok and check strict
   - Expected: config.strict_empty_collections is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwrap Ok and check strict")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5a71824a1ff36843325a0057caffbfbb68fc6ad1b9d4675269856aa589bd45f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a71824a1ff36843325a0057caffbfbb68fc6ad1b9d4675269856aa589bd45f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a71824a1ff36843325a0057caffbfbb68fc6ad1b9d4675269856aa589bd45f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/compiler/config/chained_enum_method_spec.spl
mirror: doc/06_spec/01_unit/compiler/config/chained_enum_method_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/config/chained_enum_method_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/config/chained_enum_method_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/config/chained_enum_method_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'I32 via intermediate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/config/chained_enum_method_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'I64 via intermediate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/config/chained_enum_method_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F32 via intermediate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/config/chained_enum_method_spec.spl:188:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'Test' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
