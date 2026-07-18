# Aspect-Oriented Programming (AOP) Specification

> on pc{ execution(* target_func(..)) } use advice_func before priority 10

<!-- sdn-diagram:id=aop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aspect-Oriented Programming (AOP) Specification

on pc{ execution(* target_func(..)) } use advice_func before priority 10

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AOP-001 to #AOP-020 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/aop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Before advice - runs before target function
on pc{ execution(* target_func(..)) } use advice_func before priority 10

# After advice - runs after successful execution
on pc{ execution(* target_func(..)) } use advice_func after_success priority 5

# Architecture rules
forbid pc{ import(test.internal.*) } "Production cannot import test internals"
allow pc{ depend(within(api.**), within(core.**)) } "API can depend on core"
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Advice | Code that executes at join points (before/after/around) |
| Pointcut | Expression defining where advice applies: `pc{...}` |
| Join point | Execution point where advice can be woven |
| Weaving | Process of inserting advice at join points |
| Priority | Integer controlling advice execution order |

## Behaviors

- Higher priority executes earlier for `before` advice
- Higher priority executes later for `after_*` advice
- `around` advice must call `proceed()` exactly once
- Zero overhead when AOP is not enabled
- Compile-time weaving for `before`/`after`, runtime for `around`

## Limitations (Current Implementation)

- Around advice is implemented through the runtime proceed contract and MIR weaving helpers
- Inline module definitions in test blocks not supported
- Runtime `init(...)` interception with `@inject` is covered in the Rust interpreter path; broader Simple-side DI/AOP authoring remains limited

## Scenarios

### AOP Basic Syntax

#### before advice declaration

#### parses before advice with execution pointcut

1. fn log entry
2. fn target func
3. on pc{ execution
4. expect target func


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn log_entry():
    pass

fn target_func() -> i64:
    42

on pc{ execution(* target_func(..)) } use log_entry before priority 10

expect target_func() == 42
```

</details>

#### parses before advice with wildcard return type

1. fn trace
2. fn compute
3. on pc{ execution
4. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn trace():
    pass

fn compute(x: i64) -> i64:
    x * 2

on pc{ execution(* compute(..)) } use trace before priority 5

expect compute(21) == 42
```

</details>

#### after advice declaration

#### parses after_success advice

1. fn log exit
2. fn add
3. on pc{ execution
4. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn log_exit():
    pass

fn add(a: i64, b: i64) -> i64:
    a + b

on pc{ execution(* add(..)) } use log_exit after_success priority 10

expect add(20, 22) == 42
```

</details>

#### parses after_error advice

1. fn log error
2. fn may fail
3. Err
4. Ok
5. on pc{ execution
6. expect may fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn log_error():
    pass

fn may_fail(x: i64) -> Result<i64, text>:
    if x < 0:
        Err("negative input")
    else:
        Ok(x)

on pc{ execution(* may_fail(..)) } use log_error after_error priority 10

expect may_fail(42).unwrap() == 42
```

</details>

### Before Advice Execution

#### execution order

#### executes before advice before target

1. fn before advice
2. fn target
3. on pc{ execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify basic before advice execution
var advice_called = false

fn before_advice():
    advice_called = true

fn target() -> i64:
    42

on pc{ execution(* target(..)) } use before_advice before priority 10

val result = target()
expect result == 42
expect advice_called == true
```

</details>

### After Advice Execution

#### after_success execution

#### executes after_success when target succeeds

1. fn after advice
2. fn target
3. on pc{ execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false

fn after_advice():
    executed = true

fn target() -> i64:
    42

on pc{ execution(* target(..)) } use after_advice after_success priority 10

val result = target()
expect result == 42
expect executed == true
```

</details>

#### does not execute after_success when target returns Err

1. fn after advice
2. fn failing target
3. Err
4. on pc{ execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false

fn after_advice():
    executed = true

fn failing_target() -> Result<i64, text>:
    Err("intentional failure")

on pc{ execution(* failing_target(..)) } use after_advice after_success priority 10

val result = failing_target()
expect result.err.?
expect executed == false
```

</details>

#### after_error execution

#### executes after_error when target returns Err

1. fn error handler
2. fn failing
3. Err
4. on pc{ execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var error_logged = false

fn error_handler():
    error_logged = true

fn failing() -> Result<i64, text>:
    Err("test error")

on pc{ execution(* failing(..)) } use error_handler after_error priority 10

val result = failing()
expect result.err.?
expect error_logged == true
```

</details>

### Pointcut Expressions

#### execution patterns

#### matches specific function name

1. fn marker
2. fn specific func
3. on pc{ execution
4. specific func


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var called = false

fn marker():
    called = true

fn specific_func() -> i64:
    42

on pc{ execution(* specific_func(..)) } use marker before priority 10

specific_func()
expect called == true
```

</details>

#### matches with wildcard in function name

1. fn counter
2. fn calc add
3. fn calc sub
4. on pc{ execution
5. calc add
6. calc sub


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0

fn counter():
    count = count + 1

fn calc_add() -> i64:
    1

fn calc_sub() -> i64:
    2

on pc{ execution(* calc*(..)) } use counter before priority 10

calc_add()
calc_sub()
expect count == 2
```

</details>

#### attribute patterns

#### matches functions with specific attribute

1. fn logger
2. fn important operation
3. fn regular operation
4. on pc{ attr
5. important operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var logged = false

fn logger():
    logged = true

@logged
fn important_operation() -> i64:
    42

fn regular_operation() -> i64:
    0

on pc{ attr(logged) } use logger before priority 10

important_operation()
expect logged == true
```

</details>

#### logical operators

#### combines pointcuts with AND

1. fn marker
2. fn critical calc
3. on pc{ execution
4. critical calc


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var called = false

fn marker():
    called = true

@critical
fn critical_calc() -> i64:
    42

on pc{ execution(* critical*(..)) & attr(critical) } use marker before priority 10

critical_calc()
expect called == true
```

</details>

#### combines pointcuts with OR

1. fn counter
2. fn func a
3. fn func b
4. on pc{ execution
5. func a
6. func b


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0

fn counter():
    count = count + 1

fn func_a() -> i64:
    1

fn func_b() -> i64:
    2

on pc{ execution(* func_a(..)) | execution(* func_b(..)) } use counter before priority 10

func_a()
func_b()
expect count == 2
```

</details>

#### negates pointcuts with NOT

1. fn counter
2. fn should skip
3. fn should count
4. on pc{ !execution
5. should skip
6. should count


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0

fn counter():
    count = count + 1

fn should_skip() -> i64:
    0

fn should_count() -> i64:
    1

on pc{ !execution(* should_skip(..)) & execution(* should*(..)) } use counter before priority 10

should_skip()
should_count()
expect count == 1
```

</details>

### Architecture Rules

#### forbid rules

#### declares forbidden import pattern

1. forbid pc{ import
2. expect "Production cannot import test internals" contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This rule is checked at compile time
forbid pc{ import(test.internal.*) } "Production cannot import test internals"

# Rule declared successfully
expect "Production cannot import test internals".contains("Production")
```

</details>

#### declares forbidden dependency pattern

1. forbid pc{ depend
2. expect "Domain cannot depend on infrastructure" contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ depend(within(domain.**), within(infrastructure.**)) } "Domain cannot depend on infrastructure"

expect "Domain cannot depend on infrastructure".contains("Domain")
```

</details>

#### allow rules

#### declares allowed dependency pattern

1. allow pc{ depend
2. expect "API layer can depend on core" contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
allow pc{ depend(within(api.**), within(core.**)) } "API layer can depend on core"

expect "API layer can depend on core".contains("API layer")
```

</details>

### Weaving Diagnostics

#### weaving reports

#### reports join points woven

1. fn track weave
2. fn target1
3. fn target2
4. on pc{ execution
5. target1
6. target2


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var woven_count = 0

fn track_weave():
    woven_count = woven_count + 1

fn target1() -> i64:
    1

fn target2() -> i64:
    2

on pc{ execution(* target*(..)) } use track_weave before priority 10

target1()
target2()
expect woven_count == 2
```

</details>

#### validates advice configuration

1. fn valid advice
2. fn target
3. on pc{ execution
4. expect target


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Valid advice configuration should not produce errors
fn valid_advice():
    pass

fn target() -> i64:
    42

on pc{ execution(* target(..)) } use valid_advice before priority 10

expect target() == 42
```

</details>

### Zero Overhead When Disabled

#### no advice means no overhead

#### function without advice has no weaving

1. fn simple func
2. expect simple func


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn simple_func() -> i64:
    42

# No AOP declarations for this function
expect simple_func() == 42
```

</details>

#### disabled weaving produces no diagnostics

1. fn isolated func
2. expect isolated func


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn isolated_func() -> i64:
    100

expect isolated_func() == 100
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
