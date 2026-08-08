# Basic Mixin Declaration and Application

> Mixins are stateful traits — they inject fields and methods into classes at definition time. Unlike traits (behavioral contracts for runtime dispatch), mixins provide structural composition without inheritance.

<!-- sdn-diagram:id=mixin_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixin_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixin_basic_spec -> Timestamped
mixin_basic_spec -> Trackable
mixin_basic_spec -> Valuable
mixin_basic_spec -> Scorable
mixin_basic_spec -> HasId
mixin_basic_spec -> HasName
mixin_basic_spec -> Ident
mixin_basic_spec -> Labeled
mixin_basic_spec -> Defaultable
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixin_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Mixin Declaration and Application

Mixins are stateful traits — they inject fields and methods into classes at definition time. Unlike traits (behavioral contracts for runtime dispatch), mixins provide structural composition without inheritance.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/features/mixin_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Mixins are stateful traits — they inject fields and methods into classes
at definition time. Unlike traits (behavioral contracts for runtime dispatch),
mixins provide structural composition without inheritance.

## Syntax

```simple
mixin Timestamped:
    created_at: i64
    updated_at: i64

    fn age() -> i64:
        self.updated_at - self.created_at

class User:
    use Timestamped
    name: text
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Mixin | Reusable bundle of fields and methods |
| Field injection | Mixin fields become class fields |
| Method injection | Mixin methods become class methods |
| Override | Class methods override mixin methods |

## Behavior

- Mixins inject fields into classes at definition time
- Mixins inject methods into classes (unless class defines same-named method)
- Multiple mixins can be applied to one class
- dyn Mixin is NOT supported (mixins are structural, not behavioral)

## Scenarios

### Mixin Field Injection

#### injects mixin fields into class

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Trackable:
    created_at: i64

class Item:
    use Trackable
    name: text

val item = Item(created_at: 100, name: "test")
expect item.created_at == 100
expect item.name == "test"
```

</details>

#### injects multiple fields from mixin

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Timestamped:
    created_at: i64
    updated_at: i64

class Record:
    use Timestamped
    id: i64

val r = Record(created_at: 10, updated_at: 20, id: 1)
expect r.created_at == 10
expect r.updated_at == 20
expect r.id == 1
```

</details>

### Mixin Method Injection

#### injects mixin methods into class

1. fn doubled
2. expect c doubled


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Valuable:
    amount: i64

    fn doubled() -> i64:
        return self.amount * 2

class Coin:
    use Valuable

val c = Coin(amount: 25)
expect c.doubled() == 50
```

</details>

#### injects mixin method with arguments

1. fn add score
2. expect p add score


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Scorable:
    score: i64

    fn add_score(n) -> i64:
        return self.score + n

class Player:
    use Scorable
    name: text

val p = Player(score: 10, name: "Alice")
expect p.add_score(5) == 15
```

</details>

### Multiple Mixins

#### applies two mixins to one class

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin HasId:
    id: i64

mixin HasName:
    name: text

class Entity:
    use HasId
    use HasName

val e = Entity(id: 42, name: "Alice")
expect e.id == 42
expect e.name == "Alice"
```

</details>

#### methods from both mixins available

1. fn get id
2. fn get label
3. expect w get id
4. expect w get label


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Ident:
    id: i64

    fn get_id() -> i64:
        return self.id

mixin Labeled:
    label: text

    fn get_label() -> text:
        return self.label

class Widget:
    use Ident
    use Labeled

val w = Widget(id: 7, label: "button")
expect w.get_id() == 7
expect w.get_label() == "button"
```

</details>

### Mixin Method Override

#### class method overrides mixin method

1. fn compute
2. fn compute
3. expect c compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Defaultable:
    val_: i64

    fn compute() -> i64:
        return self.val_

class Custom:
    use Defaultable

    fn compute() -> i64:
        return self.val_ * 10

val c = Custom(val_: 5)
expect c.compute() == 50
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
