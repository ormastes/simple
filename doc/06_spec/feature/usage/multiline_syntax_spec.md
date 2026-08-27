# Multi-line Syntax Specification

> Tests for multi-line syntax patterns including function calls spanning multiple lines, array literals, and continuation lines.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-line Syntax Specification

Tests for multi-line syntax patterns including function calls spanning multiple lines, array literals, and continuation lines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MULTI-001 |
| Category | Language \| Syntax |
| Status | Implemented |
| Source | `test/feature/usage/multiline_syntax_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for multi-line syntax patterns including function calls spanning
multiple lines, array literals, and continuation lines.

## Syntax

```simple
# Multi-line function call
use std.spec.step

val result = function_name(
arg1,
arg2,
arg3
)

# Multi-line array
val items = [
1,
2,
3
]

# Line continuation with backslash
val sum = 1 + 2 + \
3 + 4
```

## Scenarios

### Multi-line Function Calls

#### basic multi-line calls

#### calls function with arguments on multiple lines

- calls function with arguments on multiple lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls function with arguments on multiple lines")
fn add(a, b):
    return a + b

val result = add(
    1,
    2
)
expect result == 3
```

</details>

#### calls function with named arguments on multiple lines

- calls function with named arguments on multiple lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls function with named arguments on multiple lines")
fn greet(name, msg):
    return 42

val result = greet(
    name: "test",
    msg: "hello"
)
expect result == 42
```

</details>

#### nested function calls

#### nests function calls on single line

- nests function calls on single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("nests function calls on single line")
fn inner(x):
    return x * 2

fn outer(a, b):
    return a + b

expect outer(inner(5), inner(3)) == 16
```

</details>

#### nests function calls on multiple lines

- nests function calls on multiple lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("nests function calls on multiple lines")
fn inner(x):
    return x * 2

fn outer(a, b):
    return a + b

val result = outer(
    inner(5),
    inner(3)
)
expect result == 16
```

</details>

### Multi-line Literals

#### creates multi-line array literal

- creates multi-line array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates multi-line array literal")
val arr = [
    1,
    2,
    3
]
expect arr[0] + arr[1] + arr[2] == 6
```

</details>

#### creates multi-line struct initialization

- creates multi-line struct initialization


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates multi-line struct initialization")
struct Config:
    name: str
    value: i64

fn Config_new(name, value):
    return Config { name: name, value: value }

val c = Config_new(
    "test",
    42
)
expect c.value == 42
```

</details>

### Continuation Lines

#### continues function call to next line

- continues function call to next line


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("continues function call to next line")
fn match_exception(a, b, c):
    return 42

val result = match_exception("ValueError", "some message",
                   "expected")
expect result == 42
```

</details>

#### continues call at same indent level

- continues call at same indent level


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("continues call at same indent level")
fn match_exception(a, b, c):
    return 42

val result = match_exception("ValueError", "some message",
```

</details>

### Tuple Destructuring in Assignments

#### destructures tuple from array element

- destructures tuple from array element


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("destructures tuple from array element")
val arr = [(10, 20)]
val _pair = arr[0]
val a = _pair[0]
val b = _pair[1]
expect a + b == 30
```

</details>

#### accesses tuple elements with dot notation

- accesses tuple elements with dot notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accesses tuple elements with dot notation")
val arr = [(10, 20)]
expect arr[0].0 + arr[0].1 == 30
```

</details>

#### destructures nested tuple data

- destructures nested tuple data


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("destructures nested tuple data")
val docstrings = [("content", 1), ("other", 2)]
val _pair = docstrings[0]
val content = _pair[0]
val line = _pair[1]
expect line == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `f0ecccb30b0a70d9690c5d844d6bb03bbe3288b824cc95f799608cbbc1455d12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0ecccb30b0a70d9690c5d844d6bb03bbe3288b824cc95f799608cbbc1455d12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0ecccb30b0a70d9690c5d844d6bb03bbe3288b824cc95f799608cbbc1455d12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/multiline_syntax_spec.spl
mirror: doc/06_spec/feature/usage/multiline_syntax_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/multiline_syntax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/multiline_syntax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/multiline_syntax_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls function with arguments on multiple lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/multiline_syntax_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls function with named arguments on multiple lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/multiline_syntax_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nests function calls on single line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
