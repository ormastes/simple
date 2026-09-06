# Parser Option Coverage Specification

> Tests covering Option Generic Type Branches, Result Generic Type Branches, Unknown Generic Type Branches, Postfix ? Type Branches, Simple Type Branches, Array Type Branches.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Option Coverage Specification

## Scenarios

### Option Generic Type Branches

#### Option<i64> returns TYPE_OPTION_I64

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Option<i64> returns TYPE_OPTION_I64
   - Expected: ret equals `TYPE_OPTION_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option<i64> returns TYPE_OPTION_I64")
val ret = get_ret_type("fn f() -> Option<i64>:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION_I64)
```

</details>

#### Option<f64> returns TYPE_OPTION_F64

- Option<f64> returns TYPE_OPTION_F64
   - Expected: ret equals `TYPE_OPTION_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option<f64> returns TYPE_OPTION_F64")
val ret = get_ret_type("fn f() -> Option<f64>:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION_F64)
```

</details>

#### Option<text> returns TYPE_OPTION_TEXT

- Option<text> returns TYPE_OPTION_TEXT
   - Expected: ret equals `TYPE_OPTION_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option<text> returns TYPE_OPTION_TEXT")
val ret = get_ret_type("fn f() -> Option<text>:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION_TEXT)
```

</details>

#### Option<bool> returns TYPE_OPTION_BOOL

- Option<bool> returns TYPE_OPTION_BOOL
   - Expected: ret equals `TYPE_OPTION_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option<bool> returns TYPE_OPTION_BOOL")
val ret = get_ret_type("fn f() -> Option<bool>:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION_BOOL)
```

</details>

#### Option<CustomType> preserves the named inner type

- Option<CustomType> preserves the named inner type
   - Expected: is_option_generic_tag(ret) is true
   - Expected: inner >= TYPE_NAMED_BASE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option<CustomType> preserves the named inner type")
val ret = get_ret_type("fn f() -> Option<CustomType>:\n    nil\n")
expect(is_option_generic_tag(ret)).to_equal(true)
val inner = option_generic_type_get_inner(option_generic_tag_to_id(ret))
expect(inner >= TYPE_NAMED_BASE).to_equal(true)
```

</details>

### Result Generic Type Branches

#### Result<i64> returns TYPE_RESULT

- Result<i64> returns TYPE_RESULT
   - Expected: ret equals `TYPE_RESULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Result<i64> returns TYPE_RESULT")
val ret = get_ret_type("fn f() -> Result<i64>:\n    nil\n")
expect(ret).to_equal(TYPE_RESULT)
```

</details>

#### Result<text> returns TYPE_RESULT

- Result<text> returns TYPE_RESULT
   - Expected: ret equals `TYPE_RESULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Result<text> returns TYPE_RESULT")
val ret = get_ret_type("fn f() -> Result<text>:\n    nil\n")
expect(ret).to_equal(TYPE_RESULT)
```

</details>

### Unknown Generic Type Branches

#### List<i64> returns TYPE_ANY (unknown generic)

- List<i64> returns TYPE_ANY (unknown generic)
   - Expected: ret equals `TYPE_ANY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("List<i64> returns TYPE_ANY (unknown generic)")
val ret = get_ret_type("fn f() -> List<i64>:\n    nil\n")
expect(ret).to_equal(TYPE_ANY)
```

</details>

#### Set<text> returns TYPE_ANY (unknown generic)

- Set<text> returns TYPE_ANY (unknown generic)
   - Expected: ret equals `TYPE_ANY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Set<text> returns TYPE_ANY (unknown generic)")
val ret = get_ret_type("fn f() -> Set<text>:\n    nil\n")
expect(ret).to_equal(TYPE_ANY)
```

</details>

### Postfix ? Type Branches

#### i64? returns TYPE_OPTION_I64

- i64? returns TYPE_OPTION_I64
   - Expected: ret equals `TYPE_OPTION_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i64? returns TYPE_OPTION_I64")
val ret = get_ret_type("fn f() -> i64?:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION_I64)
```

</details>

#### f64? returns TYPE_OPTION_F64

- f64? returns TYPE_OPTION_F64
   - Expected: ret equals `TYPE_OPTION_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f64? returns TYPE_OPTION_F64")
val ret = get_ret_type("fn f() -> f64?:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION_F64)
```

</details>

#### text? returns TYPE_OPTION_TEXT

- text? returns TYPE_OPTION_TEXT
   - Expected: ret equals `TYPE_OPTION_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text? returns TYPE_OPTION_TEXT")
val ret = get_ret_type("fn f() -> text?:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION_TEXT)
```

</details>

#### bool? returns TYPE_OPTION_BOOL

- bool? returns TYPE_OPTION_BOOL
   - Expected: ret equals `TYPE_OPTION_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool? returns TYPE_OPTION_BOOL")
val ret = get_ret_type("fn f() -> bool?:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION_BOOL)
```

</details>

#### CustomType? preserves the named inner type

- CustomType? preserves the named inner type
   - Expected: is_option_generic_tag(ret) is true
   - Expected: inner >= TYPE_NAMED_BASE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CustomType? preserves the named inner type")
val ret = get_ret_type("fn f() -> CustomType?:\n    nil\n")
expect(is_option_generic_tag(ret)).to_equal(true)
val inner = option_generic_type_get_inner(option_generic_tag_to_id(ret))
expect(inner >= TYPE_NAMED_BASE).to_equal(true)
```

</details>

### Simple Type Branches

#### i64 returns TYPE_I64

- i64 returns TYPE_I64
   - Expected: ret equals `TYPE_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i64 returns TYPE_I64")
val ret = get_ret_type("fn f() -> i64:\n    0\n")
expect(ret).to_equal(TYPE_I64)
```

</details>

#### f64 returns TYPE_F64

- f64 returns TYPE_F64
   - Expected: ret equals `TYPE_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f64 returns TYPE_F64")
val ret = get_ret_type("fn f() -> f64:\n    0.0\n")
expect(ret).to_equal(TYPE_F64)
```

</details>

#### text returns TYPE_TEXT

- text returns TYPE_TEXT
   - Expected: ret equals `TYPE_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text returns TYPE_TEXT")
val ret = get_ret_type("fn f() -> text:\n    \"\"\n")
expect(ret).to_equal(TYPE_TEXT)
```

</details>

#### bool returns TYPE_BOOL

- bool returns TYPE_BOOL
   - Expected: ret equals `TYPE_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool returns TYPE_BOOL")
val ret = get_ret_type("fn f() -> bool:\n    true\n")
expect(ret).to_equal(TYPE_BOOL)
```

</details>

#### Option (bare) returns TYPE_OPTION

- Option (bare) returns TYPE_OPTION
   - Expected: ret equals `TYPE_OPTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option (bare) returns TYPE_OPTION")
val ret = get_ret_type("fn f() -> Option:\n    nil\n")
expect(ret).to_equal(TYPE_OPTION)
```

</details>

#### Result (bare) returns TYPE_RESULT

- Result (bare) returns TYPE_RESULT
   - Expected: ret equals `TYPE_RESULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Result (bare) returns TYPE_RESULT")
val ret = get_ret_type("fn f() -> Result:\n    nil\n")
expect(ret).to_equal(TYPE_RESULT)
```

</details>

#### UnknownType returns a registered named type

- UnknownType returns a registered named type
   - Expected: ret >= TYPE_NAMED_BASE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UnknownType returns a registered named type")
val ret = get_ret_type("fn f() -> UnknownType:\n    nil\n")
expect(ret >= TYPE_NAMED_BASE).to_equal(true)
```

</details>

### Array Type Branches

#### [i64] returns TYPE_ARRAY_I64

- [i64] returns TYPE_ARRAY_I64
   - Expected: ret equals `TYPE_ARRAY_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[i64] returns TYPE_ARRAY_I64")
val ret = get_ret_type("fn f() -> [i64]:\n    []\n")
expect(ret).to_equal(TYPE_ARRAY_I64)
```

</details>

#### [text] returns TYPE_ARRAY_TEXT

- [text] returns TYPE_ARRAY_TEXT
   - Expected: ret equals `TYPE_ARRAY_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[text] returns TYPE_ARRAY_TEXT")
val ret = get_ret_type("fn f() -> [text]:\n    []\n")
expect(ret).to_equal(TYPE_ARRAY_TEXT)
```

</details>

#### [bool] returns TYPE_ARRAY_BOOL

- [bool] returns TYPE_ARRAY_BOOL
   - Expected: ret equals `TYPE_ARRAY_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[bool] returns TYPE_ARRAY_BOOL")
val ret = get_ret_type("fn f() -> [bool]:\n    []\n")
expect(ret).to_equal(TYPE_ARRAY_BOOL)
```

</details>

#### [[i64]] returns TYPE_ARRAY_ANY

- [[i64]] returns TYPE_ARRAY_ANY
   - Expected: ret equals `TYPE_ARRAY_ANY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[i64]] returns TYPE_ARRAY_ANY")
val ret = get_ret_type("fn f() -> [[i64]]:\n    []\n")
expect(ret).to_equal(TYPE_ARRAY_ANY)
```

</details>

#### [[text]] returns TYPE_ARRAY_ANY

- [[text]] returns TYPE_ARRAY_ANY
   - Expected: ret equals `TYPE_ARRAY_ANY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[text]] returns TYPE_ARRAY_ANY")
val ret = get_ret_type("fn f() -> [[text]]:\n    []\n")
expect(ret).to_equal(TYPE_ARRAY_ANY)
```

</details>

#### [[bool]] returns TYPE_ARRAY_ANY

- [[bool]] returns TYPE_ARRAY_ANY
   - Expected: ret equals `TYPE_ARRAY_ANY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[bool]] returns TYPE_ARRAY_ANY")
val ret = get_ret_type("fn f() -> [[bool]]:\n    []\n")
expect(ret).to_equal(TYPE_ARRAY_ANY)
```

</details>

#### [[[i64]]] returns TYPE_ARRAY_ANY

- [[[i64]]] returns TYPE_ARRAY_ANY
   - Expected: ret equals `TYPE_ARRAY_ANY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[[[i64]]] returns TYPE_ARRAY_ANY")
val ret = get_ret_type("fn f() -> [[[i64]]]:\n    []\n")
expect(ret).to_equal(TYPE_ARRAY_ANY)
```

</details>

#### [f64] returns a generic array tag

- [f64] returns a generic array tag
   - Expected: ret >= TYPE_ARRAY_GENERIC_BASE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("[f64] returns a generic array tag")
val ret = get_ret_type("fn f() -> [f64]:\n    []\n")
expect(ret >= TYPE_ARRAY_GENERIC_BASE).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/parser_option_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Option Generic Type Branches, Result Generic Type Branches, Unknown Generic Type Branches, Postfix ? Type Branches, Simple Type Branches, Array Type Branches.
- Option Generic Type Branches
- Result Generic Type Branches
- Unknown Generic Type Branches
- Postfix ? Type Branches
- Simple Type Branches
- Array Type Branches

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `14a4a7bc30f352abb29be262a8b2fa32e85a18bc48cdd7e453321962cd45d46f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14a4a7bc30f352abb29be262a8b2fa32e85a18bc48cdd7e453321962cd45d46f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14a4a7bc30f352abb29be262a8b2fa32e85a18bc48cdd7e453321962cd45d46f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/parser_option_coverage_spec.spl
mirror: doc/06_spec/unit/compiler_core/parser_option_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/parser_option_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/parser_option_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/parser_option_coverage_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Option<i64> returns TYPE_OPTION_I64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/parser_option_coverage_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Option<f64> returns TYPE_OPTION_F64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/parser_option_coverage_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Option<text> returns TYPE_OPTION_TEXT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
