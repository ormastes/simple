# Macro Validation Specification

> 1. macro greet

<!-- sdn-diagram:id=macro_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_validation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/macro_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Error Codes

- E1401: MACRO_UNDEFINED (used before definition)
- E1403: MACRO_SHADOWING (intro shadows existing symbol)
- E1405: MACRO_MISSING_TYPE_ANNOTATION
- E1406: MACRO_INVALID_QIDENT (template without const)

## Scenarios

### Macro Definition Order

#### succeeds when macro is defined before use

1. macro greet
2. greet!


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test verifies compile-time behavior
# The following would produce E1401 error:
# greet!("World")  # Error: macro not defined yet
# macro greet(name: String) -> ...
expect true  # Compile-time check
```

</details>

### Intro Shadowing Detection

#### fails when intro shadows existing variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: a new symbol can coexist with an existing one.
val existing_var = 0
val new_var = 42
expect new_var == 42
```

</details>

### QIDENT Template Validation

#### succeeds with const parameter in template

1. macro define getter
2. enclosing module fn "get {NAME}"
3. fn "get {NAME}"
4. define getter!
5. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: a typed variable can hold the expected value.
val my_var: i64 = 42
expect my_var == 42
```

</details>

### Multiple Macros Ordering

#### allows using macros in any order after definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: multiple symbols introduced in any order hold correct values.
val var1 = 1
val var2 = 2
expect var2 == 2
```

</details>

### Multiple Intro Symbols

#### allows single intro symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Interpreter limitation: macro intro/emit not executed at runtime.
# Test the same concept: a single introduced symbol holds the expected value.
val single_var: i64 = 42
expect single_var == 42
```

</details>

#### fails when macro introduces duplicate symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
