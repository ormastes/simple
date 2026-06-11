# Class Invariant Specification

> class Counter:

<!-- sdn-diagram:id=class_invariant_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=class_invariant_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

class_invariant_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=class_invariant_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class Invariant Specification

class Counter:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONTRACT-INV-001 to #CONTRACT-INV-018 |
| Category | Type System \| Contracts |
| Status | Implemented |
| Source | `test/03_system/feature/usage/class_invariant_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
class Counter:
value: i64

invariant:
self.value >= 0

static fn new() -> Counter:
Counter(value: 0)

me increment():
self.value = self.value + 1
```

## Scenarios

### Constructor Invariant Checks

#### checks invariant after constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Counter1.new(10)
expect(c.value).to_equal(10)
```

</details>

#### checks multiple invariants after constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bc = BoundedCounter.new(5, 100)
expect(bc.value).to_equal(5)
```

</details>

#### private constructor gets invariant check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val acc = Account1.create_with_deposit(100)
expect(acc.balance).to_equal(100)
```

</details>

#### constructor with precondition and invariant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pv = PositiveValue.new(42)
expect(pv.value).to_equal(42)
```

</details>

### Public Method Invariant Checks

#### public method checks invariants

1. var c = Counter2 new
2. c increment
   - Expected: c.value equals `1`
3. c decrement
   - Expected: c.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Counter2.new()
c.increment()
expect(c.value).to_equal(1)
c.decrement()
expect(c.value).to_equal(0)
```

</details>

#### private method skips invariants

1. var c = Counter2 new
2. c increment
3. c increment
   - Expected: c.value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Counter2.new()
c.increment()
c.increment()
expect(c.value).to_equal(2)
```

</details>

#### complex invariant with field comparison

1. var r = Range1 new
2. r expand
   - Expected: r.max equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Range1.new(0, 10)
r.expand(5)
expect(r.max).to_equal(15)
```

</details>

### Multiple Classes with Invariants

#### separate invariants per class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val acc = Account2.new(100)
val tx = Transaction.new(50, 1234567890)
expect(acc.balance).to_equal(100)
expect(tx.amount).to_equal(50)
```

</details>

### Class Invariant Edge Cases

#### class without invariant works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SimpleClass.new(42)
expect(s.get_value()).to_equal(42)
```

</details>

#### invariant can reference pure methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vh = ValueHolder.new(42)
expect(vh.value).to_equal(42)
```

</details>

### Constructor Visibility

#### explicitly public constructor gets invariants

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PublicClass.new(42)
expect(p.value).to_equal(42)
```

</details>

#### constructor detected by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = Counter3.new()
val c2 = Counter3.from_value(42)
expect(c1.count).to_equal(0)
expect(c2.count).to_equal(42)
```

</details>

### Complete Class Contract Integration

#### bank account with full contracts

1. var acc = BankAccount from balance
2. acc deposit
   - Expected: acc.balance equals `150`
   - Expected: success is true
   - Expected: acc.balance equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc = BankAccount.from_balance("Alice", 100)
acc.deposit(50)
expect(acc.balance).to_equal(150)
val success = acc.withdraw(30)
expect(success).to_equal(true)
expect(acc.balance).to_equal(120)
```

</details>

### Factory Method Invariants

#### factory methods get invariants

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = ConfigObj.create_default()
val c2 = ConfigObj.from_timeout(60)
val c3 = ConfigObj.with_retries(5)
expect(c1.timeout).to_equal(30)
expect(c2.timeout).to_equal(60)
expect(c3.retries).to_equal(5)
```

</details>

### Struct Invariants

#### struct has invariant checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point1.new(3, 4)
expect(p.distance_squared()).to_equal(25)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
