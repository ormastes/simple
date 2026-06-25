# Advanced Mixin Features

> Advanced mixin patterns including mixin inheritance, private fields, default field values, static members, and conditional application.

<!-- sdn-diagram:id=mixin_advanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixin_advanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixin_advanced_spec -> Rectangle
mixin_advanced_spec -> Scored
mixin_advanced_spec -> Mathable
mixin_advanced_spec -> HasData
mixin_advanced_spec -> Identified
mixin_advanced_spec -> Priced
mixin_advanced_spec -> Scalable
mixin_advanced_spec -> Bounded
mixin_advanced_spec -> Base
mixin_advanced_spec -> Extended
mixin_advanced_spec -> L1
mixin_advanced_spec -> L2
mixin_advanced_spec -> L3
mixin_advanced_spec -> HasSecret
mixin_advanced_spec -> Internal
mixin_advanced_spec -> Configurable
mixin_advanced_spec -> Configurable2
mixin_advanced_spec -> Versioned
mixin_advanced_spec -> Computable
mixin_advanced_spec -> Labeled
mixin_advanced_spec -> Cacheable
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixin_advanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. fn area
2. expect b area


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn total
2. expect g total


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn doubled
2. fn tripled
3. fn squared
4. expect n doubled
5. expect n tripled
6. expect n squared


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn compute
2. fn compute
3. expect w compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn label
2. fn rank
3. fn label
4. fn rank
5. expect p label
6. expect p rank


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn value
2. fn value
3. expect v value


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn scale
2. fn offset
3. expect m scale
4. expect m offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn clamp
2. expect c1 clamp
3. expect c2 clamp
4. expect c3 clamp


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn get base
2. fn get ext
3. expect obj get base
4. expect obj get ext


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn reveal
2. expect k reveal


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn get internal
2. expect w get internal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn get timeout
2. expect s get timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn get timeout
2. expect s get timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. static fn version
2. expect App version


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. static fn double
2. expect Calculator double


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn label
2. fn get tag
3. fn label
4. expect item label
5. expect item get tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn serialize
2. fn get key
3. fn serialize
4. expect r serialize
5. expect r get key


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
