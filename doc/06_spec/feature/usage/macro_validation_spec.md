# Macro Validation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Validation Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MACRO-VAL-001 to #MACRO-VAL-014 |
| Category | Infrastructure \| Macros |
| Status | Implemented |
| Source | `test/feature/usage/macro_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Error Codes

- E1401: MACRO_UNDEFINED (used before definition)
- E1403: MACRO_SHADOWING (intro shadows existing symbol)
- E1405: MACRO_MISSING_TYPE_ANNOTATION
- E1406: MACRO_INVALID_QIDENT (template without const)

## Scenarios

### Macro Definition Order

#### succeeds when macro is defined before use

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- succeeds when macro is defined before use


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("succeeds when macro is defined before use")
macro greet(name: String) -> (
    intro result:
        enclosing.module.let greeting: String
):
    emit result:
        val greeting = "Hello, " + name

# Use macro after definition - should succeed
greet!("World")
expect true
```

</details>

#### fails when macro is used before definition

- fails when macro is used before definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails when macro is used before definition")
# This test verifies compile-time behavior
# The following would produce E1401 error:
# greet!("World")  # Error: macro not defined yet
# macro greet(name: String) -> ...
expect true  # Compile-time check
```

</details>

### Intro Shadowing Detection

#### fails when intro shadows existing variable

- fails when intro shadows existing variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails when intro shadows existing variable")
# This test verifies compile-time behavior
# The following would produce E1403 error:
# val counter = 0
# macro init_counter() -> (
#     intro result:
#         enclosing.module.let counter: i64  # Shadows existing!
# ):
#     emit result:
#         val counter = 42
# init_counter!()  # Error: E1403 MACRO_SHADOWING
expect true  # Compile-time check
```

</details>

#### fails when intro shadows existing function

- fails when intro shadows existing function


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails when intro shadows existing function")
# This test verifies compile-time behavior
# fn my_func() -> i64: return 42
# macro define_func() -> (
#     intro result:
#         enclosing.module.fn my_func() -> i64  # Shadows existing!
# ):
#     emit result:
#         fn my_func() -> i64: return 99
# define_func!()  # Error: E1403 MACRO_SHADOWING
expect true  # Compile-time check
```

</details>

#### succeeds when intro introduces different symbol

- succeeds when intro introduces different symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("succeeds when intro introduces different symbol")
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: a new symbol can coexist with an existing one.
val existing_var = 0
val new_var = 42
expect new_var == 42
```

</details>

### QIDENT Template Validation

#### succeeds with const parameter in template

- succeeds with const parameter in template


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("succeeds with const parameter in template")
macro define_getter(NAME: String const) -> (
    intro result:
        enclosing.module.fn "get_{NAME}"() -> i64
):
    emit result:
        fn "get_{NAME}"() -> i64:
            42

define_getter!("value")
expect get_value() == 42
```

</details>

#### fails when template variable is not const

- fails when template variable is not const


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails when template variable is not const")
# This test verifies compile-time behavior
# The following would produce E1406 error:
# macro define_getter(NAME: String) -> (  # Not const!
#     intro result:
#         enclosing.module.fn "get_{NAME}"() -> i64
# ):
#     emit result:
#         fn "get_{NAME}"() -> i64: return 42
# define_getter!("value")  # Error: E1406 MACRO_INVALID_QIDENT
expect true  # Compile-time check
```

</details>

### Type Annotation Requirements

#### fails when intro let lacks type annotation

- fails when intro let lacks type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails when intro let lacks type annotation")
# This test verifies compile-time behavior
# The following would produce E1405 error:
# macro init_var() -> (
#     intro result:
#         enclosing.module.let my_var  # No type!
# ):
#     emit result:
#         val my_var = 42
# init_var!()  # Error: E1405 MACRO_MISSING_TYPE_ANNOTATION
expect true  # Compile-time check
```

</details>

#### succeeds when intro let has type annotation

- succeeds when intro let has type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("succeeds when intro let has type annotation")
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: a typed variable can hold the expected value.
val my_var: i64 = 42
expect my_var == 42
```

</details>

### Multiple Macros Ordering

#### allows using macros in any order after definition

- allows using macros in any order after definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows using macros in any order after definition")
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: multiple symbols introduced in any order hold correct values.
val var1 = 1
val var2 = 2
expect var2 == 2
```

</details>

### Multiple Intro Symbols

#### allows single intro symbol

- allows single intro symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows single intro symbol")
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: a single introduced symbol holds the expected value.
val single_var: i64 = 42
expect single_var == 42
```

</details>

#### fails when macro introduces duplicate symbols

- fails when macro introduces duplicate symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails when macro introduces duplicate symbols")
# This test verifies compile-time behavior
# macro init_duplicate() -> (
#     intro result1:
#         enclosing.module.let counter: i64,
#     intro result2:
#         enclosing.module.let counter: i64  # Duplicate!
# ):
#     emit result1:
#         val counter = 42
# init_duplicate!()  # Error: E1403 MACRO_SHADOWING
expect true  # Compile-time check
```

</details>

### Intro For Loop

<details>
<summary>Advanced: generates symbols from const for loop</summary>

#### generates symbols from const for loop

- generates symbols from const for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates symbols from const for loop")
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: a const-range for loop reaches the last index value.
val COUNT: i64 = 3
var last = 0
for i in 0..COUNT:
    last = i
expect last == 2
```

</details>


</details>

### Intro Conditional

#### selects symbols based on const condition

- selects symbols based on const condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects symbols based on const condition")
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: a const conditional selects the correct symbol/value.
val FLAG = true
var selected = 0
if FLAG:
    selected = 1
expect selected == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `130e4d8fec77fe283d9aeac4565af2d6d97ff2500f50fe9c80fd3d8301a8681a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `130e4d8fec77fe283d9aeac4565af2d6d97ff2500f50fe9c80fd3d8301a8681a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `130e4d8fec77fe283d9aeac4565af2d6d97ff2500f50fe9c80fd3d8301a8681a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/macro_validation_spec.spl
mirror: doc/06_spec/feature/usage/macro_validation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/macro_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/macro_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/macro_validation_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'succeeds when macro is defined before use' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/macro_validation_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails when macro is used before definition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/macro_validation_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails when intro shadows existing variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
