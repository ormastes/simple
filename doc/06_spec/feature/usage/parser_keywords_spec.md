# Parser Keywords Specification

> Tests that all Simple language keywords are correctly recognized and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Keywords Specification

Tests that all Simple language keywords are correctly recognized and

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-KW-001 to #PARSER-KW-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_keywords_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests that all Simple language keywords are correctly recognized and
parsed in their appropriate contexts.

## Scenarios

### Variable Keyword Parsing

#### val declares immutable variable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- val declares immutable variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("val declares immutable variable")
val x = 42
expect x == 42
```

</details>

#### var declares mutable variable

- var declares mutable variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("var declares mutable variable")
var x = 0
x = 42
expect x == 42
```

</details>

### Control Flow Keyword Parsing

#### parses if statement

- parses if statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses if statement")
val result = if true:
    1
else:
    0
expect result == 1
```

</details>

#### parses elif statement

- parses elif statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses elif statement")
val x = 2
val result = if x == 1:
    "one"
elif x == 2:
    "two"
else:
    "other"
expect result == "two"
```

</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

- parses while loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses while loop")
var x = 0
while x < 3:
    x = x + 1
expect x == 3
```

</details>


</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

- parses for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses for loop")
var sum = 0
for i in [1, 2, 3]:
    sum = sum + i
expect sum == 6
```

</details>


</details>

<details>
<summary>Advanced: parses break in loop</summary>

#### parses break in loop

- parses break in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses break in loop")
var x = 0
while true:
    x = x + 1
    if x >= 5:
        break
expect x == 5
```

</details>


</details>

<details>
<summary>Advanced: parses continue in loop</summary>

#### parses continue in loop

- parses continue in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses continue in loop")
var sum = 0
for i in [1, 2, 3, 4, 5]:
    if i == 3:
        continue
    sum = sum + i
expect sum == 12
```

</details>


</details>

#### parses return statement

- parses return statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses return statement")
fn early_return(x: i64) -> i64:
    if x < 0:
        return 0
    x
expect early_return(-1) == 0
expect early_return(5) == 5
```

</details>

#### parses match expression

- parses match expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses match expression")
val result = match 42:
    case 0 => "zero"
    case 42 => "forty-two"
    case _ => "other"
expect result == "forty-two"
```

</details>

### Logic Keyword Parsing

#### parses and operator

- parses and operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses and operator")
expect (true and true) == true
expect (true and false) == false
expect (false and true) == false
```

</details>

#### parses or operator

- parses or operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses or operator")
expect (true or true) == true
expect (true or false) == true
expect (false or false) == false
```

</details>

#### parses not operator

- parses not operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses not operator")
expect (not false) == true
expect (not true) == false
```

</details>

#### parses in operator

- parses in operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses in operator")
expect 2 in [1, 2, 3]
expect not (5 in [1, 2, 3])
```

</details>

### Special Keyword Parsing

#### parses true

- parses true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses true")
val x = true
expect x
```

</details>

#### parses false

- parses false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses false")
val x = false
expect not x
```

</details>

#### parses nil

- parses nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses nil")
val x = nil
expect x == nil
```

</details>

#### parses self in method

- parses self in method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses self in method")
val p = TestPoint(x: 42, y: 10)
expect p.get_x() == 42
expect p.get_y() == 10
```

</details>

### Function Keyword Parsing

#### parses fn declaration

- parses fn declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses fn declaration")
fn add(a: i64, b: i64) -> i64:
    a + b
expect add(3, 4) == 7
```

</details>

#### parses nested function

- parses nested function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses nested function")
fn outer(x: i64) -> i64:
    fn inner(y: i64) -> i64:
        y * 2
    inner(x) + 1
expect outer(5) == 11
```

</details>

#### parses lambda expression

- parses lambda expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses lambda expression")
val double = \x: x * 2
expect double(5) == 10
```

</details>

#### parses higher-order function

- parses higher-order function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses higher-order function")
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)
expect apply(\n: n + 1, 5) == 6
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `31d44e6310d1934e26116777c06c78b376a7a0068864fac35f5b58203ad78179`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `31d44e6310d1934e26116777c06c78b376a7a0068864fac35f5b58203ad78179`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `31d44e6310d1934e26116777c06c78b376a7a0068864fac35f5b58203ad78179`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/parser_keywords_spec.spl
mirror: doc/06_spec/feature/usage/parser_keywords_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/parser_keywords_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/parser_keywords_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/parser_keywords_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'val declares immutable variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_keywords_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var declares mutable variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_keywords_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses if statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
