# Advanced Mixin Features

> Advanced mixin patterns including mixin inheritance, private fields, default field values, static members, and conditional application.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Mixin Features

Advanced mixin patterns including mixin inheritance, private fields, default field values, static members, and conditional application.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 3/5 |
| Status | Partial (basic mixins implemented, advanced features planned) |
| Source | `test/03_system/feature/features/mixin_advanced_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Advanced mixin patterns including mixin inheritance, private fields,
default field values, static members, and conditional application.

## Behavior

- Mixins can require other mixins (transitive composition)
- Private mixin fields are not exposed to the composing class
- Default values can be provided and overridden
- Static fields/methods in mixins are shared

## Scenarios

### Advanced Mixin Features

#### Mixin with computed methods

#### mixin method accesses multiple fields

- mixin method accesses multiple fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin method accesses multiple fields")
mixin Rectangle:
    width: i64
    height: i64

    fn area() -> i64:
        return self.width * self.height

class Box:
    use Rectangle
    depth: i64

val b = Box(width: 3, height: 4, depth: 5)
expect b.area() == 12
```

</details>

#### mixin method returns derived value

- mixin method returns derived value


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin method returns derived value")
mixin Scored:
    base: i64
    bonus: i64

    fn total() -> i64:
        return self.base + self.bonus

class Game:
    use Scored

val g = Game(base: 100, bonus: 50)
expect g.total() == 150
```

</details>

#### mixin with multiple computed methods

- mixin with multiple computed methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin with multiple computed methods")
mixin Mathable:
    val_: i64

    fn doubled() -> i64:
        return self.val_ * 2

    fn tripled() -> i64:
        return self.val_ * 3

    fn squared() -> i64:
        return self.val_ * self.val_

class Num:
    use Mathable

val n = Num(val_: 5)
expect n.doubled() == 10
expect n.tripled() == 15
expect n.squared() == 25
```

</details>

#### Mixin with trait interaction

#### trait impl uses mixin fields

- trait impl uses mixin fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("trait impl uses mixin fields")
trait Computable:
    fn compute(self) -> i64:
        return 0

mixin HasData:
    data: i64

class Worker:
    use HasData
    factor: i64

impl Computable for Worker:
    fn compute(self) -> i64:
        return self.data * self.factor

val w = Worker(data: 7, factor: 3)
expect w.compute() == 21
```

</details>

#### multiple traits on class with mixin

- multiple traits on class with mixin


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple traits on class with mixin")
trait Displayable:
    fn label(self) -> text:
        return ""

trait Rankable:
    fn rank(self) -> i64:
        return 0

mixin Identified:
    id: i64

class Player:
    use Identified
    name: text
    points: i64

impl Displayable for Player:
    fn label(self) -> text:
        return "Player {self.name} (#{self.id})"

impl Rankable for Player:
    fn rank(self) -> i64:
        return self.points

val p = Player(id: 42, name: "Alice", points: 100)
expect p.label() == "Player Alice (#42)"
expect p.rank() == 100
```

</details>

#### dyn Trait works with mixin class

- dyn Trait works with mixin class


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dyn Trait works with mixin class")
trait Valuable:
    fn value(self) -> i64:
        return 0

mixin Priced:
    price: i64

class Item:
    use Priced
    name: text

impl Valuable for Item:
    fn value(self) -> i64:
        return self.price

val item = Item(price: 50, name: "widget")
val v: dyn Valuable = item
expect v.value() == 50
```

</details>

#### Mixin method with arguments

#### mixin method takes parameters

- mixin method takes parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin method takes parameters")
mixin Scalable:
    base: i64

    fn scale(factor: i64) -> i64:
        return self.base * factor

    fn offset(amount: i64) -> i64:
        return self.base + amount

class Metric:
    use Scalable

val m = Metric(base: 10)
expect m.scale(3) == 30
expect m.offset(5) == 15
```

</details>

#### mixin method with multiple parameters

- mixin method with multiple parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin method with multiple parameters")
mixin Bounded:
    val_: i64

    fn clamp(lo: i64, hi: i64) -> i64:
        if self.val_ < lo:
            return lo
        if self.val_ > hi:
            return hi
        return self.val_

class Clamped:
    use Bounded

val c1 = Clamped(val_: 5)
expect c1.clamp(0, 10) == 5
val c2 = Clamped(val_: -3)
expect c2.clamp(0, 10) == 0
val c3 = Clamped(val_: 15)
expect c3.clamp(0, 10) == 10
```

</details>

#### Mixin inheritance

#### mixin can use another mixin

- mixin can use another mixin


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin can use another mixin")
mixin Base:
    base_val: i64

    fn get_base() -> i64:
        return self.base_val

mixin Extended:
    use Base
    ext_val: i64

    fn get_ext() -> i64:
        return self.ext_val

class MyClass:
    use Extended

val obj = MyClass(base_val: 10, ext_val: 20)
expect obj.get_base() == 10
expect obj.get_ext() == 20
```

</details>

#### inherits all fields transitively

- inherits all fields transitively


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inherits all fields transitively")
mixin L1:
    a: i64

mixin L2:
    use L1
    b: i64

mixin L3:
    use L2
    c: i64

class ThreeLevel:
    use L3

val obj = ThreeLevel(a: 1, b: 2, c: 3)
expect obj.a == 1
expect obj.b == 2
expect obj.c == 3
```

</details>

#### Private fields in mixins

#### supports private mixin fields

- supports private mixin fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports private mixin fields")
mixin HasSecret:
    _secret: i64

    fn reveal() -> i64:
        return self._secret

class Keeper:
    use HasSecret
    name: text

val k = Keeper(_secret: 42, name: "keeper")
expect k.reveal() == 42
```

</details>

#### private fields not exposed to class

- private fields not exposed to class


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("private fields not exposed to class")
mixin Internal:
    _internal: i64

    fn get_internal() -> i64:
        return self._internal * 2

class Wrapper:
    use Internal
    pub_val: i64

val w = Wrapper(_internal: 5, pub_val: 10)
expect w.get_internal() == 10
expect w.pub_val == 10
```

</details>

#### Default field values

#### mixins can provide default values

- mixins can provide default values


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixins can provide default values")
mixin Configurable:
    timeout: i64 = 30
    retries: i64 = 3

    fn get_timeout() -> i64:
        return self.timeout

class Service:
    use Configurable
    name: text

val s = Service(name: "api")
expect s.get_timeout() == 30
expect s.retries == 3
```

</details>

#### class can override defaults

- class can override defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("class can override defaults")
mixin Configurable2:
    timeout: i64 = 30

    fn get_timeout() -> i64:
        return self.timeout

class Service2:
    use Configurable2
    name: text

val s = Service2(timeout: 60, name: "api")
expect s.get_timeout() == 60
```

</details>

#### Mixin with static members

#### supports static fields in mixins

- supports static fields in mixins


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports static fields in mixins")
mixin Versioned:
    ver: i64

    static fn version() -> i64:
        return 1

class App:
    use Versioned

expect App.version() == 1
```

</details>

#### supports static methods in mixins

- supports static methods in mixins


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports static methods in mixins")
mixin Computable:
    val_: i64

    static fn double(n: i64) -> i64:
        return n * 2

class Calculator:
    use Computable

expect Calculator.double(5) == 10
```

</details>

#### Conditional mixin application

#### applies mixin based on trait

- applies mixin based on trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies mixin based on trait")
trait Printable:
    fn label(self) -> text:
        return ""

mixin Labeled:
    tag: text

    fn get_tag() -> text:
        return self.tag

class Item:
    use Labeled
    name: text

impl Printable for Item:
    fn label(self) -> text:
        return "{self.name}: {self.tag}"

val item = Item(tag: "urgent", name: "task")
expect item.label() == "task: urgent"
expect item.get_tag() == "urgent"
```

</details>

#### validates conditions at compile time

- validates conditions at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates conditions at compile time")
trait Serializable:
    fn serialize(self) -> text:
        return ""

mixin Cacheable:
    cache_key: text

    fn get_key() -> text:
        return self.cache_key

class Record:
    use Cacheable
    data: text

impl Serializable for Record:
    fn serialize(self) -> text:
        return "{self.cache_key}:{self.data}"

val r = Record(cache_key: "k1", data: "hello")
expect r.serialize() == "k1:hello"
expect r.get_key() == "k1"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `78949efb47662499261eb3ea899b554e2c7df7349f8cb8c265a51adadecd684a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78949efb47662499261eb3ea899b554e2c7df7349f8cb8c265a51adadecd684a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78949efb47662499261eb3ea899b554e2c7df7349f8cb8c265a51adadecd684a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/mixin_advanced_spec.spl
mirror: doc/06_spec/03_system/feature/features/mixin_advanced_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/mixin_advanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/mixin_advanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/mixin_advanced_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mixin method accesses multiple fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/mixin_advanced_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mixin method returns derived value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/mixin_advanced_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mixin with multiple computed methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
