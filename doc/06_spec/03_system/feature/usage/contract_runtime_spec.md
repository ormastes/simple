# Contract Runtime Specification

> fn transfer(from: i64, to: i64, amount: i64) -> (i64, i64):

<!-- sdn-diagram:id=contract_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=contract_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

contract_runtime_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=contract_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract Runtime Specification

fn transfer(from: i64, to: i64, amount: i64) -> (i64, i64):

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONTRACT-RT-001 to #CONTRACT-RT-031 |
| Category | Type System \| Contracts |
| Status | Implemented |
| Source | `test/03_system/feature/usage/contract_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Contract Syntax

```simple
fn transfer(from: i64, to: i64, amount: i64) -> (i64, i64):
in:
amount > 0
from >= amount
invariant:
from >= 0
to >= 0
out(res):
res.0 == old(from) - amount
res.1 == old(to) + amount
# function body
```

## Scenarios

### Basic old() Capture

#### captures simple parameter value

1. fn increment
2. out
3. ret == old
4. expect increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn increment(x: i64) -> i64:
    out(ret):
        ret == old(x) + 1
    x + 1
expect increment(41) == 42
```

</details>

#### captures multiple parameters

1. fn swap and sum
2. out
3. ret == old
4. expect swap and sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn swap_and_sum(a: i64, b: i64) -> i64:
    out(ret):
        ret == old(a) + old(b)
    a + b
expect swap_and_sum(20, 22) == 42
```

</details>

#### captures field access

1. me increment
2. out
3. self value == old
4. var c = Counter
5. c increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    value: i64

    me increment():
        out(_):
            self.value == old(self.value) + 1
        self.value = self.value + 1

var c = Counter(value: 41)
c.increment()
expect c.value == 42
```

</details>

#### captures complex expression

1. fn double and square
2. out
3. ret ==
4. expect double and square


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double_and_square(x: i64) -> i64:
    out(ret):
        ret == (old(x) * 2) * (old(x) * 2)
    val doubled = x * 2
    doubled * doubled
expect double_and_square(3) == 36
```

</details>

### Precondition Lowering

#### validates basic precondition

1. fn divide
2. expect divide


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn divide(a: i64, b: i64) -> i64:
    in:
        b != 0
    a / b
expect divide(84, 2) == 42
```

</details>

#### validates multiple preconditions

1. fn bounded divide
2. expect bounded divide


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn bounded_divide(a: i64, b: i64, max: i64) -> i64:
    in:
        b != 0
        a >= 0
        b > 0
        max > 0
        a <= max
    a / b
expect bounded_divide(84, 2, 100) == 42
```

</details>

### Postcondition Lowering

#### validates basic postcondition

1. fn abs value
2. out
3. expect abs value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn abs_value(x: i64) -> i64:
    out(ret):
        ret >= 0
    if x < 0:
        -x
    else:
        x
expect abs_value(-42) == 42
```

</details>

#### validates multiple postconditions

1. fn compute positive
2. out
3. expect compute positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compute_positive(x: i64) -> i64:
    out(ret):
        ret > 0
        ret >= x
        ret <= x + 100
    x + 10
expect compute_positive(32) == 42
```

</details>

### Invariant Lowering

#### validates basic invariant

1. fn process
2. expect process


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process(x: i64) -> i64:
    invariant:
        x >= 0
    x + 1
expect process(41) == 42
```

</details>

### Combined Contracts with old()

#### validates transfer function

1. fn transfer
2. out
3. res 0 == old
4. res 1 == old
5. res 0 + res 1 == old
6.


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transfer(from_balance: i64, to_balance: i64, amount: i64) -> (i64, i64):
    in:
        amount > 0
        from_balance >= amount
    invariant:
        from_balance >= 0
        to_balance >= 0
    out(res):
        res.0 == old(from_balance) - amount
        res.1 == old(to_balance) + amount
        res.0 + res.1 == old(from_balance) + old(to_balance)
    val new_from = from_balance - amount
    val new_to = to_balance + amount
    (new_from, new_to)

val (from, to) = transfer(100, 50, 30)
expect from == 70
expect to == 80
```

</details>

#### validates custom binding in postcondition

1. fn compute
2. out
3. res > old
4. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compute(x: i64) -> i64:
    out(res):
        res > old(x)
    x + 10
expect compute(32) == 42
```

</details>

### Multiple old() References

#### handles multiple references to same old()

1. fn double check
2. out
3. ret == old
4. ret > old
5. ret - old
6. expect double check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double_check(x: i64) -> i64:
    out(ret):
        ret == old(x) * 2
        ret > old(x)
        ret - old(x) == old(x)
    x * 2
expect double_check(21) == 42
```

</details>

#### handles old() with different params

1. fn combine
2. out
3. ret > old
4. ret > old
5. ret > old
6. ret == old
7. expect combine


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn combine(x: i64, y: i64, z: i64) -> i64:
    out(ret):
        ret > old(x)
        ret > old(y)
        ret > old(z)
        ret == old(x) + old(y) + old(z)
    x + y + z
expect combine(10, 15, 17) == 42
```

</details>

### Error Postconditions

#### parses error postcondition

1. fn divide safe
2. out
3. expect divide safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn divide_safe(a: i64, b: i64) -> i64:
    in:
        b != 0
    out(ret):
        ret == a / b
    a / b
expect divide_safe(84, 2) == 42
```

</details>

#### validates success and error postconditions

1. fn validate age
2. out
3. expect validate age


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn validate_age(age: i64) -> bool:
    in:
        age >= 0
    out(ret):
        ret == true or ret == false
    if age >= 18:
        true
    else:
        false
expect validate_age(21) == true
```

</details>

### Complex Contract Scenarios

#### validates nested old expressions

1. fn complex math
2. out
3. ret ==
4. ret > old
5. ret > old
6.
7. expect complex math


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn complex_math(x: i64, y: i64) -> i64:
    out(ret):
        ret == (old(x) + old(y)) * 2
        ret > old(x)
        ret > old(y)
    (x + y) * 2
expect complex_math(10, 11) == 42
```

</details>

#### validates arithmetic contracts

1. fn increment by ten
2. out
3. ret == old
4. ret - old
5. expect increment by ten


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn increment_by_ten(x: i64) -> i64:
    out(ret):
        ret == old(x) + 10
        ret - old(x) == 10
    x + 10
expect increment_by_ten(32) == 42
```

</details>

#### validates comparison chain contracts

1. fn clamp
2. out
3. expect clamp
4. expect clamp
5. expect clamp


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn clamp(x: i64, min: i64, max: i64) -> i64:
    in:
        min <= max
        min >= 0
        max >= 0
    out(ret):
        ret >= min
        ret <= max
    if x < min:
        min
    elif x > max:
        max
    else:
        x
expect clamp(42, 0, 100) == 42
expect clamp(200, 0, 100) == 100
expect clamp(-10, 0, 100) == 0
```

</details>

### All Contract Types Together

#### validates full contract

1. fn full contract
2. out
3. ret > old
4. ret > old
5. ret == old
6. expect full contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn full_contract(x: i64, y: i64) -> i64:
    in:
        x > 0
        y > 0
    invariant:
        x > 0
        y > 0
    out(ret):
        ret > old(x)
        ret > old(y)
        ret == old(x) + old(y)
    x + y
expect full_contract(20, 22) == 42
```

</details>

### Contract with Boolean Logic

#### validates boolean logic contract

1. fn validate range
2. out
3. expect validate range


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn validate_range(x: i64, y: i64) -> bool:
    in:
        x >= 0
        y >= 0
    out(ret):
        ret == true
    x >= 0 and y >= 0
expect validate_range(10, 20) == true
```

</details>

#### validates negation contract

1. fn ensure nonzero
2. out
3. expect ensure nonzero


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn ensure_nonzero(x: i64) -> i64:
    in:
        x != 0
    out(ret):
        ret != 0
    x
expect ensure_nonzero(42) == 42
```

</details>

### Contract with Conditionals

#### validates conditional contract

1. fn abs with contract
2. out
3. expect abs with contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn abs_with_contract(x: i64) -> i64:
    out(ret):
        ret >= 0
    if x >= 0:
        x
    else:
        -x
expect abs_with_contract(-42) == 42
```

</details>

#### validates early return contract

1. fn early exit
2. out
3. expect early exit
4. expect early exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn early_exit(x: i64) -> i64:
    in:
        x >= 0
    out(ret):
        ret >= 0
    if x == 0:
        return 1
    x
expect early_exit(0) == 1
expect early_exit(42) == 42
```

</details>

### old() with Arithmetic Expressions

#### captures arithmetic in old()

1. fn double and increment
2. out
3. ret ==
4. expect double and increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double_and_increment(x: i64) -> i64:
    out(ret):
        ret == (old(x) * 2) + 1
    val doubled = x * 2
    doubled + 1
expect double_and_increment(20) == 41
```

</details>

#### references parameter in postcondition

1. fn sum with check
2. out
3. expect sum with check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_with_check(a: i64, b: i64) -> i64:
    out(ret):
        ret >= a
        ret >= b
    a + b
expect sum_with_check(20, 22) == 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
