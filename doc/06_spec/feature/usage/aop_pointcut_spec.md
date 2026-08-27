# AOP Pointcut Expression Specification

> pc{ selector(pattern) }

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# AOP Pointcut Expression Specification

pc{ selector(pattern) }

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AOP-PC-001 to #AOP-PC-015 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/aop_pointcut_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
pc{ selector(pattern) }
pc{ selector1(...) & selector2(...) }  # AND
pc{ selector1(...) | selector2(...) }  # OR
pc{ !selector(...) }                   # NOT
```

## Selectors

| Selector | Description | Example |
|----------|-------------|---------|
| execution | Match function execution | `execution(* foo(..))` |
| within | Match code in module/class | `within(services.*)` |
| attr | Match by attribute | `attr(logged)` |

## Limitations (Current Implementation)

- Init selector not yet implemented (requires around advice)
- Inline module definitions in test blocks not supported

## Scenarios

### Execution Pointcut Selector

#### return type patterns

#### matches any return type with wildcard

- matches any return type with wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches any return type with wildcard")
var matched = false

fn marker():
    matched = true

fn returns_int() -> i64:
    42

fn returns_text() -> text:
    "hello"

on pc{ execution(* returns*(..)) } use marker before priority 10

returns_int()
expect matched == true

matched = false
returns_text()
expect matched == true
```

</details>

#### function name patterns

#### matches exact function name

- matches exact function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches exact function name")
var called = false

fn marker():
    called = true

fn exact_name() -> i64:
    42

fn other_name() -> i64:
    0

on pc{ execution(* exact_name(..)) } use marker before priority 10

exact_name()
expect called == true
```

</details>

#### matches prefix wildcard

- matches prefix wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches prefix wildcard")
var count = 0

fn counter():
    count = count + 1

fn handle_request() -> i64:
    1

fn handle_response() -> i64:
    2

fn process_data() -> i64:
    3

on pc{ execution(* handle*(..)) } use counter before priority 10

handle_request()
handle_response()
process_data()
expect count == 2
```

</details>

#### matches suffix wildcard

- matches suffix wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches suffix wildcard")
var count = 0

fn counter():
    count = count + 1

fn get_user() -> i64:
    1

fn get_order() -> i64:
    2

fn set_user() -> i64:
    3

on pc{ execution(* get*(..)) } use counter before priority 10

get_user()
get_order()
set_user()
expect count == 2
```

</details>

#### parameter patterns

#### matches any parameters with (..)

- matches any parameters with (..)


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches any parameters with (..)")
var called = false

fn marker():
    called = true

fn no_params() -> i64:
    1

fn one_param(x: i64) -> i64:
    x

fn two_params(x: i64, y: i64) -> i64:
    x + y

on pc{ execution(* *_params(..)) } use marker before priority 10

no_params()
expect called == true

called = false
one_param(1)
expect called == true

called = false
two_params(1, 2)
expect called == true
```

</details>

### Attribute Pointcut Selector

#### function attributes

#### matches function with attribute

- matches function with attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches function with attribute")
var logged = false

fn logger():
    logged = true

@traced
fn traced_operation() -> i64:
    42

fn untraced_operation() -> i64:
    0

on pc{ attr(traced) } use logger before priority 10

traced_operation()
expect logged == true

logged = false
untraced_operation()
expect logged == false
```

</details>

#### matches multiple attributes

- matches multiple attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches multiple attributes")
var count = 0

fn counter():
    count = count + 1

@critical
@logged
fn important() -> i64:
    42

@logged
fn regular() -> i64:
    0

on pc{ attr(critical) & attr(logged) } use counter before priority 10

important()
expect count == 1

regular()
expect count == 1  # Still 1, regular doesn't have @critical
```

</details>

### Pointcut Logical Operators

#### AND operator

#### requires both conditions

- requires both conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("requires both conditions")
var called = false

fn marker():
    called = true

@important
fn important_calc() -> i64:
    42

fn regular_calc() -> i64:
    0

@important
fn important_other() -> i64:
    1

on pc{ execution(* *_calc(..)) & attr(important) } use marker before priority 10

important_calc()
expect called == true

called = false
regular_calc()
expect called == false  # Missing @important

called = false
important_other()
expect called == false  # Not *_calc
```

</details>

#### OR operator

#### matches either condition

- matches either condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches either condition")
var count = 0

fn counter():
    count = count + 1

fn option_a() -> i64:
    1

fn option_b() -> i64:
    2

fn option_c() -> i64:
    3

on pc{ execution(* option_a(..)) | execution(* option_b(..)) } use counter before priority 10

option_a()
option_b()
option_c()
expect count == 2
```

</details>

#### NOT operator

#### excludes matching pointcuts

- excludes matching pointcuts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("excludes matching pointcuts")
var count = 0

fn counter():
    count = count + 1

fn included() -> i64:
    1

fn excluded() -> i64:
    2

on pc{ execution(* *(..)) & !execution(* excluded(..)) } use counter before priority 10

included()
excluded()
expect count == 1
```

</details>

### Wildcard Patterns in Pointcuts

#### prefix and suffix wildcards

#### matches prefix with name*

- matches prefix with name*


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches prefix with name*")
var count = 0

fn counter():
    count = count + 1

fn get_user() -> i64:
    1

fn get_order() -> i64:
    2

fn set_user() -> i64:
    3

on pc{ execution(* get*(..)) } use counter before priority 10

get_user()
get_order()
set_user()
expect count == 2
```

</details>

#### matches suffix with *name

- matches suffix with *name


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches suffix with *name")
var count = 0

fn counter():
    count = count + 1

fn user_service() -> i64:
    1

fn order_service() -> i64:
    2

fn user_controller() -> i64:
    3

on pc{ execution(* *_service(..)) } use counter before priority 10

user_service()
order_service()
user_controller()
expect count == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `0b3be21ddbb4996754439ffae34854229ba34c772fe98ece679df99e8d58eb39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b3be21ddbb4996754439ffae34854229ba34c772fe98ece679df99e8d58eb39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b3be21ddbb4996754439ffae34854229ba34c772fe98ece679df99e8d58eb39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/aop_pointcut_spec.spl
mirror: doc/06_spec/feature/usage/aop_pointcut_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/aop_pointcut_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/aop_pointcut_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/aop_pointcut_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches any return type with wildcard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/aop_pointcut_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches exact function name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/aop_pointcut_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches prefix wildcard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
