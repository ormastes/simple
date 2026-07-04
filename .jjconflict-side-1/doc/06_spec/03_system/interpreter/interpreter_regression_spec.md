# Interpreter Regression Specification

> 1. var sm = StateMachine

<!-- sdn-diagram:id=interpreter_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_regression_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Regression Specification

## Scenarios

### Bug 1a - fn methods read state correctly

#### match on self.state works in fn method

1. var sm = StateMachine
   - Expected: sm.read_with_match() equals `active:running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = StateMachine(state: Status.Active("running"), log: "")
expect(sm.read_with_match()).to_equal("active:running")
```

</details>

#### if-val on self.state works in fn method

1. var sm = StateMachine
   - Expected: sm.read_with_if_val() equals `active:running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = StateMachine(state: Status.Active("running"), log: "")
expect(sm.read_with_if_val()).to_equal("active:running")
```

</details>

#### match on Error state works in fn method

1. var sm = StateMachine
   - Expected: sm.read_with_match() equals `error:broken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = StateMachine(state: Status.Error("broken"), log: "")
expect(sm.read_with_match()).to_equal("error:broken")
```

</details>

#### if-val on Error state works in fn method

1. var sm = StateMachine
   - Expected: sm.read_with_if_val() equals `error:broken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = StateMachine(state: Status.Error("broken"), log: "")
expect(sm.read_with_if_val()).to_equal("error:broken")
```

</details>

### Bug 1b - me methods read state correctly

#### match on self.state works in me method

1. var sm = StateMachine
2. var result = sm mutate and read match
   - Expected: result equals `active:running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = StateMachine(state: Status.Active("running"), log: "")
var result = sm.mutate_and_read_match("updated")
expect(result).to_equal("active:running")
```

</details>

#### if-val on self.state works in me method

1. var sm = StateMachine
2. var result = sm mutate and read if val
   - Expected: result equals `active:running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = StateMachine(state: Status.Active("running"), log: "")
var result = sm.mutate_and_read_if_val("updated")
expect(result).to_equal("active:running")
```

</details>

#### match on Error state works in me method

1. var sm = StateMachine
2. var result = sm mutate and read match
   - Expected: result equals `error:broken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = StateMachine(state: Status.Error("broken"), log: "")
var result = sm.mutate_and_read_match("updated")
expect(result).to_equal("error:broken")
```

</details>

#### if-val on Error state works in me method

1. var sm = StateMachine
2. var result = sm mutate and read if val
   - Expected: result equals `error:broken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = StateMachine(state: Status.Error("broken"), log: "")
var result = sm.mutate_and_read_if_val("updated")
expect(result).to_equal("error:broken")
```

</details>

### Bug 1c - impl block methods with pattern matching

#### then_match works on resolved promise

1. var p = Promise
2. var result = p then match
   - Expected: result.is_resolved() is true
   - Expected: result.get_value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Resolved(21), data: 0)
var result = p.then_match(_1 * 2)
expect(result.is_resolved()).to_equal(true)
expect(result.get_value()).to_equal(42)
```

</details>

#### then_if_val works on resolved promise

1. var p = Promise
2. var result = p then if val
   - Expected: result.is_resolved() is true
   - Expected: result.get_value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Resolved(21), data: 0)
var result = p.then_if_val(_1 * 2)
expect(result.is_resolved()).to_equal(true)
expect(result.get_value()).to_equal(42)
```

</details>

#### then_match propagates rejection

1. var p = Promise
2. var result = p then match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Rejected("fail"), data: 0)
var result = p.then_match(\v: v)
match result.state:
    case Rejected(e): expect(e).to_equal("fail")
    case _: expect(true).to_equal(false)
```

</details>

#### then_if_val propagates rejection

1. var p = Promise
2. var result = p then if val


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Rejected("fail"), data: 0)
var result = p.then_if_val(\v: v)
match result.state:
    case Rejected(e): expect(e).to_equal("fail")
    case _: expect(true).to_equal(false)
```

</details>

### Bug 2 - Function-typed class fields

#### class with fn-typed field can be constructed

1. fn double
2. var h = Holder
   - Expected: h.value equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2
var h = Holder(value: 10, compute: double)
expect(h.value).to_equal(10)
```

</details>

#### fn-typed field can be accessed and called

1. fn triple
2. var h = Holder
   - Expected: f(7) equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn triple(x: i64) -> i64:
    x * 3
var h = Holder(value: 5, compute: triple)
var f = h.compute
expect(f(7)).to_equal(21)
```

</details>

#### lambda in fn-typed field works

1. var h = Holder
   - Expected: f(42) equals `142`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = Holder(value: 1, compute: \x: x + 100)
var f = h.compute
expect(f(42)).to_equal(142)
```

</details>

### Bug 3 - Array .len() corruption

#### local array .len() returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
expect(arr.len()).to_equal(3)
```

</details>

#### local array .len() called twice returns same value

1. var a = arr len
2. var b = arr len
   - Expected: a equals `5`
   - Expected: b equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
var a = arr.len()
var b = arr.len()
expect(a).to_equal(5)
expect(b).to_equal(5)
```

</details>

#### module-level array .len() returns correct value first call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(module_array.len()).to_equal(5)
```

</details>

#### module-level array .len() called twice returns same value

1. var result = get len twice
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = get_len_twice()
expect(result).to_equal(10)
```

</details>

<details>
<summary>Advanced: .len() in a loop stays correct</summary>

#### .len() in a loop stays correct

1. total = total + arr len
   - Expected: total equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
var total = 0
for i in 0..5:
    total = total + arr.len()
expect(total).to_equal(25)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/interpreter/interpreter_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bug 1a - fn methods read state correctly
- Bug 1b - me methods read state correctly
- Bug 1c - impl block methods with pattern matching
- Bug 2 - Function-typed class fields
- Bug 3 - Array .len() corruption

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
