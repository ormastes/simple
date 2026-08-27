# Basic Mixin Declaration and Application

> Mixins are stateful traits — they inject fields and methods into classes at definition time. Unlike traits (behavioral contracts for runtime dispatch), mixins provide structural composition without inheritance.

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
| Updated | 2026-08-26 |
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

- injects mixin fields into class


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("injects mixin fields into class")
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

- injects multiple fields from mixin


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("injects multiple fields from mixin")
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

- injects mixin methods into class


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("injects mixin methods into class")
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

- injects mixin method with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("injects mixin method with arguments")
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

- applies two mixins to one class


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies two mixins to one class")
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

- methods from both mixins available


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("methods from both mixins available")
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

- class method overrides mixin method


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("class method overrides mixin method")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ac790a1f045d8f481dcb12109b6adb5de56fb3cea556ad5fb7fec1f81e9fde51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac790a1f045d8f481dcb12109b6adb5de56fb3cea556ad5fb7fec1f81e9fde51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac790a1f045d8f481dcb12109b6adb5de56fb3cea556ad5fb7fec1f81e9fde51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/mixin_basic_spec.spl
mirror: doc/06_spec/03_system/feature/features/mixin_basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/mixin_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/mixin_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/mixin_basic_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects mixin fields into class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/mixin_basic_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects multiple fields from mixin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/mixin_basic_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects mixin methods into class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
