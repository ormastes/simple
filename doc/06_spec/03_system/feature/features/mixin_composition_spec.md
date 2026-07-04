# Mixin Composition and Ordering

> Composing multiple mixins with proper field and method resolution. Tests application order, field shadowing, and method overriding.

<!-- sdn-diagram:id=mixin_composition_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixin_composition_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixin_composition_spec -> First
mixin_composition_spec -> Second
mixin_composition_spec -> Alpha
mixin_composition_spec -> Beta
mixin_composition_spec -> MA
mixin_composition_spec -> MB
mixin_composition_spec -> MC
mixin_composition_spec -> M1
mixin_composition_spec -> M2
mixin_composition_spec -> Base
mixin_composition_spec -> P
mixin_composition_spec -> Q
mixin_composition_spec -> HasX
mixin_composition_spec -> HasY
mixin_composition_spec -> HasSum
mixin_composition_spec -> Taggable
mixin_composition_spec -> Shared
mixin_composition_spec -> Left
mixin_composition_spec -> Right
mixin_composition_spec -> A
mixin_composition_spec -> B
mixin_composition_spec -> Level1
mixin_composition_spec -> Level2
mixin_composition_spec -> C
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixin_composition_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mixin Composition and Ordering

Composing multiple mixins with proper field and method resolution. Tests application order, field shadowing, and method overriding.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 3/5 |
| Status | Partial (basic composition implemented, advanced resolution planned) |
| Source | `test/03_system/feature/features/mixin_composition_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Composing multiple mixins with proper field and method resolution.
Tests application order, field shadowing, and method overriding.

## Behavior

- Mixins are applied in declaration order
- Later mixins can shadow fields from earlier ones
- Class methods always override mixin methods
- Diamond composition deduplicates shared mixins

## Scenarios

### Mixin Composition

#### Basic composition order

#### fields from multiple mixins are accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin First:
    a: i64

mixin Second:
    b: i64

class Combined:
    use First
    use Second
    c: i64

val obj = Combined(a: 1, b: 2, c: 3)
expect obj.a == 1
expect obj.b == 2
expect obj.c == 3
```

</details>

#### methods from multiple mixins resolve

1. fn get x
2. fn get y
3. expect p get x
4. expect p get y


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Alpha:
    x: i64

    fn get_x() -> i64:
        return self.x

mixin Beta:
    y: i64

    fn get_y() -> i64:
        return self.y

class Pair:
    use Alpha
    use Beta

val p = Pair(x: 10, y: 20)
expect p.get_x() == 10
expect p.get_y() == 20
```

</details>

#### three mixins compose correctly

1. fn get a
2. fn get b
3. fn get c
4. expect t get a
5. expect t get b
6. expect t get c


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin MA:
    a: i64
    fn get_a() -> i64:
        return self.a

mixin MB:
    b: i64
    fn get_b() -> i64:
        return self.b

mixin MC:
    c: i64
    fn get_c() -> i64:
        return self.c

class Triple:
    use MA
    use MB
    use MC

val t = Triple(a: 1, b: 2, c: 3)
expect t.get_a() == 1
expect t.get_b() == 2
expect t.get_c() == 3
```

</details>

#### Method resolution order

#### first mixin method wins when names conflict

1. fn value
2. fn value
3. expect b value


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin M1:
    x: i64
    fn value() -> i64:
        return self.x

mixin M2:
    y: i64
    fn value() -> i64:
        return self.y

class Both:
    use M1
    use M2

val b = Both(x: 10, y: 20)
expect b.value() == 10
```

</details>

#### class method beats mixin method

1. fn value
2. fn value
3. expect o value


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Base:
    n: i64

    fn value() -> i64:
        return self.n

class Override:
    use Base

    fn value() -> i64:
        return self.n * 100

val o = Override(n: 3)
expect o.value() == 300
```

</details>

#### class method overrides even with multiple mixins

1. fn result
2. fn result
3. fn result
4. expect pq result


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin P:
    p: i64
    fn result() -> i64:
        return self.p

mixin Q:
    q: i64
    fn result() -> i64:
        return self.q

class PQ:
    use P
    use Q

    fn result() -> i64:
        return self.p + self.q

val pq = PQ(p: 3, q: 7)
expect pq.result() == 10
```

</details>

#### Cross-mixin method calls

#### mixin method can call methods from other mixins on same class

1. fn get x
2. fn get y
3. fn compute sum
4. expect s compute sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin HasX:
    x: i64
    fn get_x() -> i64:
        return self.x

mixin HasY:
    y: i64
    fn get_y() -> i64:
        return self.y

mixin HasSum:
    fn compute_sum() -> i64:
        return self.get_x() + self.get_y()

class XYSum:
    use HasX
    use HasY
    use HasSum

val s = XYSum(x: 10, y: 20)
expect s.compute_sum() == 30
```

</details>

#### Mixin reuse across classes

#### same mixin applied to multiple classes

1. fn get tag
2. expect d get tag
3. expect i get tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Taggable:
    tag: text

    fn get_tag() -> text:
        return self.tag

class Doc:
    use Taggable
    content: text

class Image:
    use Taggable
    width: i64

val d = Doc(tag: "important", content: "hello")
val i = Image(tag: "photo", width: 800)
expect d.get_tag() == "important"
expect i.get_tag() == "photo"
```

</details>

#### Diamond composition

#### handles diamond mixin hierarchy

1. fn get id


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Shared:
    id: i64

    fn get_id() -> i64:
        return self.id

mixin Left:
    use Shared
    left_val: i64

mixin Right:
    use Shared
    right_val: i64

class Diamond:
    use Left
    use Right

val d = Diamond(id: 1, left_val: 2, right_val: 3)
expect d.id == 1
expect d.left_val == 2
expect d.right_val == 3
```

</details>

#### shared mixin applied once

1. fn get base
2. expect obj get base


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Base:
    base: i64

    fn get_base() -> i64:
        return self.base

mixin A:
    use Base
    a: i64

mixin B:
    use Base
    b: i64

class AB:
    use A
    use B

val obj = AB(base: 10, a: 20, b: 30)
expect obj.get_base() == 10
expect obj.a == 20
expect obj.b == 30
```

</details>

#### Deep composition

#### supports nested mixin composition

1. fn get x
2. fn get y
3. expect d get x
4. expect d get y


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin Level1:
    x: i64

    fn get_x() -> i64:
        return self.x

mixin Level2:
    use Level1
    y: i64

    fn get_y() -> i64:
        return self.y

class Deep:
    use Level2

val d = Deep(x: 1, y: 2)
expect d.get_x() == 1
expect d.get_y() == 2
```

</details>

#### resolves all fields correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mixin A:
    a: i64

mixin B:
    use A
    b: i64

mixin C:
    use B
    c: i64

class Chain:
    use C

val obj = Chain(a: 1, b: 2, c: 3)
expect obj.a == 1
expect obj.b == 2
expect obj.c == 3
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
