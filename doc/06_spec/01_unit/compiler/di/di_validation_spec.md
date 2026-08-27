# Di Validation Specification

> Tests covering Constructor Injection Validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Validation Specification

## Scenarios

### Constructor Injection Validation

#### accepts all params with @inject

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts all params with @inject
   - Expected: result.ok is true
   - Expected: result.error_kind equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts all params with @inject")
val ctor = ConstructorInfo.create(
    "UserService",
    has_sys_inject: false,
    params: [
        ParamInfo.create("db", "Database", true),
        ParamInfo.create("cache", "Cache", true)
    ]
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(true)
expect(result.error_kind).to_equal("")
```

</details>

#### accepts no params with @inject

- accepts no params with @inject
   - Expected: result.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts no params with @inject")
val ctor = ConstructorInfo.create(
    "Config",
    has_sys_inject: false,
    params: [
        ParamInfo.create("name", "text", false),
        ParamInfo.create("value", "i64", false)
    ]
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(true)
```

</details>

#### accepts @sys.inject on class with no param annotations

- accepts @sys.inject on class with no param annotations
   - Expected: result.ok is true
   - Expected: result.error_kind equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts @sys.inject on class with no param annotations")
val ctor = ConstructorInfo.create(
    "OrderService",
    has_sys_inject: true,
    params: [
        ParamInfo.create("repo", "OrderRepository", false),
        ParamInfo.create("payment", "PaymentService", false)
    ]
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(true)
expect(result.error_kind).to_equal("")
```

</details>

#### rejects mixed injection

- rejects mixed injection
   - Expected: result.ok is false
   - Expected: result.error_kind equals `MixedInjection`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects mixed injection")
val ctor = ConstructorInfo.create(
    "UserService",
    has_sys_inject: false,
    params: [
        ParamInfo.create("db", "Database", true),
        ParamInfo.create("config", "Config", false)
    ]
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(false)
expect(result.error_kind).to_equal("MixedInjection")
```

</details>

#### rejects mixing @sys.inject with @inject on params

- rejects mixing @sys.inject with @inject on params
   - Expected: result.ok is false
   - Expected: result.error_kind equals `MixedAnnotations`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects mixing @sys.inject with @inject on params")
val ctor = ConstructorInfo.create(
    "PaymentService",
    has_sys_inject: true,
    params: [
        ParamInfo.create("gateway", "Gateway", true),
        ParamInfo.create("logger", "Logger", false)
    ]
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(false)
expect(result.error_kind).to_equal("MixedAnnotations")
```

</details>

#### accepts empty params

- accepts empty params
   - Expected: result.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts empty params")
val ctor = ConstructorInfo.create(
    "EmptyService",
    has_sys_inject: false,
    params: []
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(true)
```

</details>

#### accepts @sys.inject with empty params

- accepts @sys.inject with empty params
   - Expected: result.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts @sys.inject with empty params")
val ctor = ConstructorInfo.create(
    "Marker",
    has_sys_inject: true,
    params: []
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(true)
```

</details>

#### rejects when only some of three params have @inject

- rejects when only some of three params have @inject
   - Expected: result.ok is false
   - Expected: result.error_kind equals `MixedInjection`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when only some of three params have @inject")
val ctor = ConstructorInfo.create(
    "Multi",
    has_sys_inject: false,
    params: [
        ParamInfo.create("a", "A", true),
        ParamInfo.create("b", "B", false),
        ParamInfo.create("c", "C", true)
    ]
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(false)
expect(result.error_kind).to_equal("MixedInjection")
```

</details>

#### error message contains class name for MixedInjection

- error message contains class name for MixedInjection
   - Expected: result.ok is false
   - Expected: result.message contains `BrokenService`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error message contains class name for MixedInjection")
val ctor = ConstructorInfo.create(
    "BrokenService",
    has_sys_inject: false,
    params: [
        ParamInfo.create("a", "A", true),
        ParamInfo.create("b", "B", false)
    ]
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(false)
expect(result.message.contains("BrokenService")).to_equal(true)
```

</details>

#### error message contains class name for MixedAnnotations

- error message contains class name for MixedAnnotations
   - Expected: result.ok is false
   - Expected: result.message contains `AnnotatedService`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error message contains class name for MixedAnnotations")
val ctor = ConstructorInfo.create(
    "AnnotatedService",
    has_sys_inject: true,
    params: [
        ParamInfo.create("dep", "Dep", true)
    ]
)
val result = validate_constructor(ctor)
expect(result.ok).to_equal(false)
expect(result.message.contains("AnnotatedService")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/di/di_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Constructor Injection Validation.
- Constructor Injection Validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `5be2b38e1087d51c60fde826f949e54fa0c158d1eddbf17da0b67fad68fe30c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5be2b38e1087d51c60fde826f949e54fa0c158d1eddbf17da0b67fad68fe30c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5be2b38e1087d51c60fde826f949e54fa0c158d1eddbf17da0b67fad68fe30c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/di/di_validation_spec.spl
mirror: doc/06_spec/01_unit/compiler/di/di_validation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/di/di_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/di/di_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/di/di_validation_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts all params with @inject' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/di/di_validation_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts no params with @inject' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/di/di_validation_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts @sys.inject on class with no param annotations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
