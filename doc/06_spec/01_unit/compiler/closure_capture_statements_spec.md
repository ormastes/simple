# closure_capture_statements_spec

> Closure Capture Must See Every Statement Kind

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# closure_capture_statements_spec

Closure Capture Must See Every Statement Kind

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/closure_capture_statements_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Closure Capture Must See Every Statement Kind

Bug doc: doc/08_tracking/bug/closure_selective_capture_skips_non_expression_statements_2026-07-27.md

Closures use SELECTIVE capture: only the identifiers a free-variable walker
finds in the body are copied into the captured environment. The walker used to
descend into `Node::Expression` statements only, so an outer value read solely
from a `val` initializer, an assignment, an `if`/`for`/`while`/`match` body, or
a `return` was never captured. At runtime the name was then simply absent:
a hard `variable X not found` inside sspec, and a SILENT `0` in ordinary code
under the JIT — an assertion written that way passed vacuously.

The smoking gun this spec pins: an earlier plain-expression read of a fixture
used to "rescue" a later `val` read of the same name in the same closure body.
Every shape below must work on its own, in any order.

The other half is shadowing: a name bound INSIDE the closure (`val`, a `for`
binder, a match pattern, a nested lambda parameter) must not drag the outer
value in — while a binder's own initializer (`val fx = fx + 1`) still reads the
outer one, because it is evaluated before the binder exists.

Deliberately NOT pinned here: how long a block-local binder lives after its
block. `val fx = 55` inside an `if` body and a `for fx in ...` binder both leak
into the enclosing scope today, identically inside and outside closures, and the
JIT and interpreter disagree about the `if` case (55 vs 10 — see
build/capfix/scope_probe.spl). That is a pre-existing block-scope-lifetime
question, unrelated to capture, so this spec asserts only what is unambiguous.

## Scenarios

### closure capture reaches every statement kind

#### captures a fixture read only from a val initializer

- captures a fixture read only from a val initializer
   - Expected: a equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a val initializer")
val a = fx
expect(a).to_equal(10)
```

</details>

#### captures a fixture read only from a var initializer

- captures a fixture read only from a var initializer
   - Expected: a equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a var initializer")
var a = fx
expect(a).to_equal(10)
```

</details>

#### captures a fixture read only from an assignment value

- captures a fixture read only from an assignment value
   - Expected: a equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from an assignment value")
var a = 0
a = fx
expect(a).to_equal(10)
```

</details>

#### captures a fixture read only from an if condition

- captures a fixture read only from an if condition
   - Expected: seen equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from an if condition")
var seen = 0
if fx > 5:
    seen = 1
expect(seen).to_equal(1)
```

</details>

#### captures a fixture read only from an if body

- captures a fixture read only from an if body
   - Expected: a equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from an if body")
var a = 0
if true:
    a = fx
expect(a).to_equal(10)
```

</details>

#### captures a fixture read only from an else body

- captures a fixture read only from an else body
   - Expected: a equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from an else body")
var a = 0
if false:
    a = 1
else:
    a = fx
expect(a).to_equal(10)
```

</details>

#### captures a fixture read only from a for iterable

- captures a fixture read only from a for iterable
   - Expected: total equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a for iterable")
var total = 0
for v in fxs:
    total = total + v
expect(total).to_equal(6)
```

</details>

#### captures a fixture read only from a for body

- captures a fixture read only from a for body
   - Expected: total equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a for body")
var total = 0
for i in [1, 2]:
    total = total + fx
expect(total).to_equal(20)
```

</details>

#### captures a fixture read only from a while condition

- captures a fixture read only from a while condition
   - Expected: n equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a while condition")
var n = 0
while n < fx:
    n = n + 5
expect(n).to_equal(10)
```

</details>

#### captures a fixture read only from a while body

- captures a fixture read only from a while body
   - Expected: n equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a while body")
var n = 0
var guard = 0
while guard < 1:
    n = fx
    guard = 1
expect(n).to_equal(10)
```

</details>

#### captures a fixture read only from a match subject

- captures a fixture read only from a match subject
   - Expected: label equals `ten`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a match subject")
var label = "none"
match fx:
    case 10:
        label = "ten"
    case _:
        label = "other"
expect(label).to_equal("ten")
```

</details>

#### captures a fixture read only from a match arm body

- captures a fixture read only from a match arm body
   - Expected: a equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a match arm body")
var a = 0
match 1:
    case 1:
        a = fx
    case _:
        a = 0
expect(a).to_equal(10)
```

</details>

#### captures a fixture read only from a nested lambda body

- captures a fixture read only from a nested lambda body
   - Expected: f() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a nested lambda body")
val f = fn() -> i64: fx
expect(f()).to_equal(10)
```

</details>

#### captures a fixture read only from a return inside a nested lambda

- captures a fixture read only from a return inside a nested lambda
   - Expected: f() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read only from a return inside a nested lambda")
val f = fn() -> i64:
    return fx
expect(f()).to_equal(10)
```

</details>

<details>
<summary>Advanced: captures a fixture read from a nested block inside a loop</summary>

#### captures a fixture read from a nested block inside a loop

- captures a fixture read from a nested block inside a loop
   - Expected: total equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures a fixture read from a nested block inside a loop")
var total = 0
for i in [1, 2]:
    if i > 1:
        total = total + fx
expect(total).to_equal(10)
```

</details>


</details>

#### needs no earlier plain-expression read to rescue a later val read

- needs no earlier plain-expression read to rescue a later val read
   - Expected: a equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("needs no earlier plain-expression read to rescue a later val read")
# The order-dependence smoking gun: this used to pass ONLY when a bare
# `fx` or `expect(fx)` statement came first.
val a = fx + 0
expect(a).to_equal(10)
```

</details>

### closure capture honours shadowing

#### a val binder inside the closure shadows the fixture

- a val binder inside the closure shadows the fixture
   - Expected: fx equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a val binder inside the closure shadows the fixture")
val fx = 99
expect(fx).to_equal(99)
```

</details>

#### a binder initializer still reads the fixture it shadows

- a binder initializer still reads the fixture it shadows
   - Expected: fx equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a binder initializer still reads the fixture it shadows")
val fx = fx + 1
expect(fx).to_equal(11)
```

</details>

<details>
<summary>Advanced: a for binder shadows the fixture inside the loop</summary>

#### a for binder shadows the fixture inside the loop

- a for binder shadows the fixture inside the loop
   - Expected: last equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a for binder shadows the fixture inside the loop")
var last = 0
for fx in [7]:
    last = fx
expect(last).to_equal(7)
```

</details>


</details>

<details>
<summary>Advanced: the fixture is still readable before a shadowing loop runs</summary>

#### the fixture is still readable before a shadowing loop runs

- the fixture is still readable before a shadowing loop runs
   - Expected: fx equals `10`
   - Expected: last equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the fixture is still readable before a shadowing loop runs")
expect(fx).to_equal(10)
var last = 0
for fx in [7]:
    last = fx
expect(last).to_equal(7)
```

</details>


</details>

#### a nested lambda parameter shadows the fixture

- a nested lambda parameter shadows the fixture
   - Expected: f(3) equals `3`
   - Expected: fx equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a nested lambda parameter shadows the fixture")
val f = fn(fx: i64) -> i64: fx
expect(f(3)).to_equal(3)
expect(fx).to_equal(10)
```

</details>

#### a shadowing binder inside an if body wins inside that body

- a shadowing binder inside an if body wins inside that body
   - Expected: fx equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a shadowing binder inside an if body wins inside that body")
if true:
    val fx = 55
    expect(fx).to_equal(55)
```

</details>

### closure capture outside sspec never silently yields 0

#### a direct read inside a fn() block keeps its value

- a direct read inside a fn() block keeps its value
   - Expected: plain_direct_read() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a direct read inside a fn() block keeps its value")
expect(plain_direct_read()).to_equal(10)
```

</details>

#### a val initializer read inside a fn() block keeps its value

- a val initializer read inside a fn() block keeps its value
   - Expected: plain_let_read() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a val initializer read inside a fn() block keeps its value")
expect(plain_let_read()).to_equal(10)
```

</details>

#### an arithmetic val read inside a fn() block keeps its value

- an arithmetic val read inside a fn() block keeps its value
   - Expected: plain_let_arith_read() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("an arithmetic val read inside a fn() block keeps its value")
expect(plain_let_arith_read()).to_equal(11)
```

</details>

#### an assignment read inside a fn() block keeps its value

- an assignment read inside a fn() block keeps its value
   - Expected: plain_assignment_read() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("an assignment read inside a fn() block keeps its value")
expect(plain_assignment_read()).to_equal(10)
```

</details>

#### a for-body read inside a fn() block keeps its value

- a for-body read inside a fn() block keeps its value
   - Expected: plain_for_read() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a for-body read inside a fn() block keeps its value")
expect(plain_for_read()).to_equal(20)
```

</details>

#### an if-body read inside a fn() block keeps its value

- an if-body read inside a fn() block keeps its value
   - Expected: plain_if_read() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("an if-body read inside a fn() block keeps its value")
expect(plain_if_read()).to_equal(10)
```

</details>

#### a shadowing val inside a fn() block wins over the outer value

- a shadowing val inside a fn() block wins over the outer value
   - Expected: plain_shadowing_let() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a shadowing val inside a fn() block wins over the outer value")
expect(plain_shadowing_let()).to_equal(99)
```

</details>

#### a shadowing binder initializer still reads the outer value

- a shadowing binder initializer still reads the outer value
   - Expected: plain_shadowing_initializer() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a shadowing binder initializer still reads the outer value")
expect(plain_shadowing_initializer()).to_equal(11)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3f4fc9249f028423f3ced26a1165c260a19e343ed4d0c8fc7da8eb4e964aab6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3f4fc9249f028423f3ced26a1165c260a19e343ed4d0c8fc7da8eb4e964aab6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3f4fc9249f028423f3ced26a1165c260a19e343ed4d0c8fc7da8eb4e964aab6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/closure_capture_statements_spec.spl
mirror: doc/06_spec/01_unit/compiler/closure_capture_statements_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/closure_capture_statements_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/closure_capture_statements_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/closure_capture_statements_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 31 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/closure_capture_statements_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures a fixture read only from a val initializer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/closure_capture_statements_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures a fixture read only from a var initializer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/closure_capture_statements_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures a fixture read only from an assignment value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
