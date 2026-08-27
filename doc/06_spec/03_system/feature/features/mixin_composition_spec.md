# Mixin Composition and Ordering

> Composing multiple mixins with proper field and method resolution. Tests application order, field shadowing, and method overriding.

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
| Updated | 2026-08-26 |
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

- fields from multiple mixins are accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fields from multiple mixins are accessible")
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

- methods from multiple mixins resolve


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("methods from multiple mixins resolve")
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

- three mixins compose correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("three mixins compose correctly")
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

- first mixin method wins when names conflict


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("first mixin method wins when names conflict")
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

- class method beats mixin method


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("class method beats mixin method")
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

- class method overrides even with multiple mixins


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("class method overrides even with multiple mixins")
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

- mixin method can call methods from other mixins on same class


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin method can call methods from other mixins on same class")
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

- same mixin applied to multiple classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("same mixin applied to multiple classes")
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

- handles diamond mixin hierarchy


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles diamond mixin hierarchy")
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

- shared mixin applied once


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shared mixin applied once")
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

- supports nested mixin composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports nested mixin composition")
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

- resolves all fields correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves all fields correctly")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ff348e2a87b422f64014b76cbf9424147e4c4ab4c0706f6b413a247fd83273fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff348e2a87b422f64014b76cbf9424147e4c4ab4c0706f6b413a247fd83273fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff348e2a87b422f64014b76cbf9424147e4c4ab4c0706f6b413a247fd83273fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/mixin_composition_spec.spl
mirror: doc/06_spec/03_system/feature/features/mixin_composition_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/mixin_composition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/mixin_composition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/mixin_composition_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fields from multiple mixins are accessible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/mixin_composition_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'methods from multiple mixins resolve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/mixin_composition_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'three mixins compose correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
