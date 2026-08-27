# Contract Runtime Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract Runtime Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONTRACT-RT-001 to #CONTRACT-RT-031 |
| Category | Type System \| Contracts |
| Status | Implemented |
| Source | `test/03_system/feature/usage/contract_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Contract Syntax

```simple
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- captures simple parameter value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures simple parameter value")
fn increment(x: i64) -> i64:
    out(ret):
        ret == old(x) + 1
    x + 1
expect increment(41) == 42
```

</details>

#### captures multiple parameters

- captures multiple parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures multiple parameters")
fn swap_and_sum(a: i64, b: i64) -> i64:
    out(ret):
        ret == old(a) + old(b)
    a + b
expect swap_and_sum(20, 22) == 42
```

</details>

#### captures field access

- captures field access


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures field access")
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

- captures complex expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures complex expression")
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

- validates basic precondition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates basic precondition")
fn divide(a: i64, b: i64) -> i64:
    in:
        b != 0
    a / b
expect divide(84, 2) == 42
```

</details>

#### validates multiple preconditions

- validates multiple preconditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates multiple preconditions")
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

- validates basic postcondition


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates basic postcondition")
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

- validates multiple postconditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates multiple postconditions")
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

- validates basic invariant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates basic invariant")
fn process(x: i64) -> i64:
    invariant:
        x >= 0
    x + 1
expect process(41) == 42
```

</details>

### Combined Contracts with old()

#### validates transfer function

- validates transfer function


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates transfer function")
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

- validates custom binding in postcondition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates custom binding in postcondition")
fn compute(x: i64) -> i64:
    out(res):
        res > old(x)
    x + 10
expect compute(32) == 42
```

</details>

### Multiple old() References

#### handles multiple references to same old()

- handles multiple references to same old()


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles multiple references to same old()")
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

- handles old() with different params


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles old() with different params")
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

- parses error postcondition


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses error postcondition")
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

- validates success and error postconditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates success and error postconditions")
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

- validates nested old expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates nested old expressions")
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

- validates arithmetic contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates arithmetic contracts")
fn increment_by_ten(x: i64) -> i64:
    out(ret):
        ret == old(x) + 10
        ret - old(x) == 10
    x + 10
expect increment_by_ten(32) == 42
```

</details>

#### validates comparison chain contracts

- validates comparison chain contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates comparison chain contracts")
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

- validates full contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates full contract")
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

- validates boolean logic contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates boolean logic contract")
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

- validates negation contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates negation contract")
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

- validates conditional contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates conditional contract")
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

- validates early return contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates early return contract")
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

- captures arithmetic in old()


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures arithmetic in old()")
fn double_and_increment(x: i64) -> i64:
    out(ret):
        ret == (old(x) * 2) + 1
    val doubled = x * 2
    doubled + 1
expect double_and_increment(20) == 41
```

</details>

#### references parameter in postcondition

- references parameter in postcondition


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("references parameter in postcondition")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fea5ff4e4b2379c2ce348993cd4bd40a0fd3536d79bff5e35019b54ee0d6499a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fea5ff4e4b2379c2ce348993cd4bd40a0fd3536d79bff5e35019b54ee0d6499a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fea5ff4e4b2379c2ce348993cd4bd40a0fd3536d79bff5e35019b54ee0d6499a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/contract_runtime_spec.spl
mirror: doc/06_spec/03_system/feature/usage/contract_runtime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/contract_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/contract_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/contract_runtime_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures simple parameter value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/contract_runtime_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures multiple parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/contract_runtime_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures field access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
