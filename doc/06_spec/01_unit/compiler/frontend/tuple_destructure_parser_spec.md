# Tuple Destructure Parser Specification

> Tests covering tuple destructuring: parser round-trip regression, tuple destructuring: val over a literal tuple, tuple destructuring: var over a literal tuple with reassignment, tuple destructuring: underscore skipping, tuple destructuring: general fallback path over a non-literal initializer, tuple destructuring: single-evaluation guarantee, tuple destructuring: nested use after destructure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tuple Destructure Parser Specification

## Scenarios

### tuple destructuring: parser round-trip regression

#### binds the real identifier name, never the literal string Ident

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds the real identifier name, never the literal string Ident


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds the real identifier name, never the literal string Ident")
val (a, b) = (10, 20)
check(a == 10)
check(b == 20)
```

</details>

#### binds a variable literally named Ident to its own value, not itself as a name

- binds a variable literally named Ident to its own value, not itself as a name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds a variable literally named Ident to its own value, not itself as a name")
val (Ident, other) = (11, 22)
check(Ident == 11)
check(other == 22)
```

</details>

#### accepts a soft-keyword-shaped identifier as a destructured name

- accepts a soft-keyword-shaped identifier as a destructured name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a soft-keyword-shaped identifier as a destructured name")
val (type, count) = (33, 44)
check(type == 33)
check(count == 44)
```

</details>

### tuple destructuring: val over a literal tuple

#### destructures a two-element literal tuple

- destructures a two-element literal tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destructures a two-element literal tuple")
val (a, b) = (1, 2)
check(a == 1)
check(b == 2)
```

</details>

#### destructures a three-element literal tuple

- destructures a three-element literal tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destructures a three-element literal tuple")
val (a, b, c) = (1, 2, 3)
check(a == 1)
check(b == 2)
check(c == 3)
```

</details>

#### keeps destructured values usable in later expressions

- keeps destructured values usable in later expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps destructured values usable in later expressions")
val (x, y) = (3, 4)
val sum_sq = x * x + y * y
check(sum_sq == 25)
```

</details>

### tuple destructuring: var over a literal tuple with reassignment

#### creates independently reassignable bindings

- creates independently reassignable bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates independently reassignable bindings")
var (x, y) = (10, 20)
x = x + 1
check(x == 11)
check(y == 20)
```

</details>

#### reassigning one binding never disturbs the others

- reassigning one binding never disturbs the others


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassigning one binding never disturbs the others")
var (a, b, c) = (1, 2, 3)
b = 99
check(a == 1)
check(b == 99)
check(c == 3)
```

</details>

### tuple destructuring: underscore skipping

#### skips a leading wildcard element

- skips a leading wildcard element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips a leading wildcard element")
val (_, kept) = (1, 2)
check(kept == 2)
```

</details>

#### skips a middle wildcard element among three

- skips a middle wildcard element among three


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips a middle wildcard element among three")
val (first, _, third) = (1, 2, 3)
check(first == 1)
check(third == 3)
```

</details>

#### skips multiple wildcard elements

- skips multiple wildcard elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips multiple wildcard elements")
val (_, keep, _) = (1, 2, 3)
check(keep == 2)
```

</details>

### tuple destructuring: general fallback path over a non-literal initializer

#### destructures the return value of a plain function call

- destructures the return value of a plain function call


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destructures the return value of a plain function call")
fn make_result() -> (i64, text, i64):
    (0, "err", 42)
val (out, err, code) = make_result()
check(out == 0)
check(err == "err")
check(code == 42)
```

</details>

#### destructures a tuple value held in a prior binding

- destructures a tuple value held in a prior binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destructures a tuple value held in a prior binding")
val prebuilt = (7, 8)
val (p, q) = prebuilt
check(p == 7)
check(q == 8)
```

</details>

### tuple destructuring: single-evaluation guarantee

#### evaluates a side-effecting initializer expression exactly once

- evaluates a side-effecting initializer expression exactly once


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates a side-effecting initializer expression exactly once")
class Counter:
    calls: i64
    me bump():
        self.calls = self.calls + 1

fn make_pair(c: Counter) -> (i64, i64):
    c.bump()
    (7, 8)

var counter = Counter(calls: 0)
val (out1, out2) = make_pair(counter)
check(out1 == 7)
check(out2 == 8)
check(counter.calls == 1)
```

</details>

### tuple destructuring: nested use after destructure

#### feeds destructured bindings into a subsequent computation

- feeds destructured bindings into a subsequent computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("feeds destructured bindings into a subsequent computation")
val (width, height) = (6, 7)
var area = width * height
val (extra_w, extra_h) = (1, 1)
area = area + extra_w * height + extra_h * width
check(area == 42 + 6 + 7)
```

</details>

#### supports destructuring twice in sequence into fresh names

- supports destructuring twice in sequence into fresh names


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports destructuring twice in sequence into fresh names")
val (a1, b1) = (1, 2)
val (a2, b2) = (a1 + b1, a1 * b1)
check(a2 == 3)
check(b2 == 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/tuple_destructure_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tuple destructuring: parser round-trip regression, tuple destructuring: val over a literal tuple, tuple destructuring: var over a literal tuple with reassignment, tuple destructuring: underscore skipping, tuple destructuring: general fallback path over a non-literal initializer, tuple destructuring: single-evaluation guarantee, tuple destructuring: nested use after destructure.
- tuple destructuring: parser round-trip regression
- tuple destructuring: val over a literal tuple
- tuple destructuring: var over a literal tuple with reassignment
- tuple destructuring: underscore skipping
- tuple destructuring: general fallback path over a non-literal initializer
- tuple destructuring: single-evaluation guarantee
- tuple destructuring: nested use after destructure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `697de56ff5e2f5827e8aa245f4d513f3ca970e8b69e78bc6360d256b45c3b325`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `697de56ff5e2f5827e8aa245f4d513f3ca970e8b69e78bc6360d256b45c3b325`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `697de56ff5e2f5827e8aa245f4d513f3ca970e8b69e78bc6360d256b45c3b325`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/tuple_destructure_parser_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/tuple_destructure_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/tuple_destructure_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/tuple_destructure_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/tuple_destructure_parser_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the real identifier name, never the literal string Ident' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/tuple_destructure_parser_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds a variable literally named Ident to its own value, not itself as a name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/tuple_destructure_parser_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a soft-keyword-shaped identifier as a destructured name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
