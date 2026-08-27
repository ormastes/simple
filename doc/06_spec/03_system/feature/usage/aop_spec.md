# Aspect-Oriented Programming (AOP) Specification

> on pc{ execution(* target_func(..)) } use advice_func before priority 10

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
| Updated | 2026-08-26 |
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

- parses before advice with execution pointcut


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses before advice with execution pointcut")
fn log_entry():
    pass

fn target_func() -> i64:
    42

on pc{ execution(* target_func(..)) } use log_entry before priority 10

expect target_func() == 42
```

</details>

#### parses before advice with wildcard return type

- parses before advice with wildcard return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses before advice with wildcard return type")
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

- parses after_success advice


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses after_success advice")
fn log_exit():
    pass

fn add(a: i64, b: i64) -> i64:
    a + b

on pc{ execution(* add(..)) } use log_exit after_success priority 10

expect add(20, 22) == 42
```

</details>

#### parses after_error advice

- parses after_error advice


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses after_error advice")
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

- executes before advice before target


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes before advice before target")
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

- executes after_success when target succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes after_success when target succeeds")
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

- does not execute after_success when target returns Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not execute after_success when target returns Err")
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

- executes after_error when target returns Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes after_error when target returns Err")
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

- matches specific function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches specific function name")
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

- matches with wildcard in function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches with wildcard in function name")
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

- matches functions with specific attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches functions with specific attribute")
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

- combines pointcuts with AND


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines pointcuts with AND")
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

- combines pointcuts with OR


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines pointcuts with OR")
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

- negates pointcuts with NOT


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("negates pointcuts with NOT")
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

- declares forbidden import pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares forbidden import pattern")
# This rule is checked at compile time
forbid pc{ import(test.internal.*) } "Production cannot import test internals"

# Rule declared successfully
expect "Production cannot import test internals".contains("Production")
```

</details>

#### declares forbidden dependency pattern

- declares forbidden dependency pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares forbidden dependency pattern")
forbid pc{ depend(within(domain.**), within(infrastructure.**)) } "Domain cannot depend on infrastructure"

expect "Domain cannot depend on infrastructure".contains("Domain")
```

</details>

#### allow rules

#### declares allowed dependency pattern

- declares allowed dependency pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares allowed dependency pattern")
allow pc{ depend(within(api.**), within(core.**)) } "API layer can depend on core"

expect "API layer can depend on core".contains("API layer")
```

</details>

### Weaving Diagnostics

#### weaving reports

#### reports join points woven

- reports join points woven


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports join points woven")
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

- validates advice configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates advice configuration")
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

- function without advice has no weaving


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function without advice has no weaving")
fn simple_func() -> i64:
    42

# No AOP declarations for this function
expect simple_func() == 42
```

</details>

#### disabled weaving produces no diagnostics

- disabled weaving produces no diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disabled weaving produces no diagnostics")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f8e383e4d4c6c7734d6b1c86eb29fe90a2192160e220f8881132c67697b46149`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8e383e4d4c6c7734d6b1c86eb29fe90a2192160e220f8881132c67697b46149`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8e383e4d4c6c7734d6b1c86eb29fe90a2192160e220f8881132c67697b46149`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/aop_spec.spl
mirror: doc/06_spec/03_system/feature/usage/aop_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/aop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/aop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/aop_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses before advice with execution pointcut' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/aop_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses before advice with wildcard return type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/aop_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses after_success advice' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
