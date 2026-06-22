# AOP Pointcut Expression Specification

> pc{ selector(pattern) }

<!-- sdn-diagram:id=aop_pointcut_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_pointcut_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_pointcut_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_pointcut_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/aop_pointcut_spec.spl` |
| Updated | 2026-06-01 |
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

1. fn marker
2. fn returns int
3. fn returns text
4. on pc{ execution
5. returns int
6. returns text


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn marker
2. fn exact name
3. fn other name
4. on pc{ execution
5. exact name


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn counter
2. fn handle request
3. fn handle response
4. fn process data
5. on pc{ execution
6. handle request
7. handle response
8. process data


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn counter
2. fn get user
3. fn get order
4. fn set user
5. on pc{ execution
6. get user
7. get order
8. set user


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn marker
2. fn no params
3. fn one param
4. fn two params
5. on pc{ execution
6. no params
7. one param
8. two params


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn logger
2. fn traced operation
3. fn untraced operation
4. on pc{ attr
5. traced operation
6. untraced operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn counter
2. fn important
3. fn regular
4. on pc{ attr
5. important
6. regular


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn marker
2. fn important calc
3. fn regular calc
4. fn important other
5. on pc{ execution
6. important calc
7. regular calc
8. important other


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn counter
2. fn option a
3. fn option b
4. fn option c
5. on pc{ execution
6. option a
7. option b
8. option c


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn counter
2. fn included
3. fn excluded
4. on pc{ execution
5. included
6. excluded


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn counter
2. fn get user
3. fn get order
4. fn set user
5. on pc{ execution
6. get user
7. get order
8. set user


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn counter
2. fn user service
3. fn order service
4. fn user controller
5. on pc{ execution
6. User service
7. order service
8. User controller


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
