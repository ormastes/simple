# Elif Val/Var Pattern Binding Specification

> Tests for `elif val`/`elif var` pattern binding in conditional branches. Verifies that pattern matching works correctly in elif positions, matching the existing `if val` support.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elif Val/Var Pattern Binding Specification

Tests for `elif val`/`elif var` pattern binding in conditional branches. Verifies that pattern matching works correctly in elif positions, matching the existing `if val` support.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1001 |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/elif_val_pattern_binding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `elif val`/`elif var` pattern binding in conditional branches.
Verifies that pattern matching works correctly in elif positions,
matching the existing `if val` support.

## Syntax

```simple
if val Some(x) = expr1:
use(x)
elif val Some(y) = expr2:
use(y)
elif condition:
fallback()
else:
default()
```

## Scenarios

### Elif Val Pattern Binding

#### basic elif val matching

#### matches elif val when if condition is false

- matches elif val when if condition is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches elif val when if condition is false")
val x = Some(42)
var result = ""
if false:
    result = "if"
elif val Some(n) = x:
    result = "elif={n}"
expect result == "elif=42"
```

</details>

#### skips elif val when pattern does not match

- skips elif val when pattern does not match


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips elif val when pattern does not match")
var result = "default"
if false:
    result = "if"
elif val Some(n) = None:
    result = "elif={n}"
expect result == "default"
```

</details>

#### binds variable from elif val pattern

- binds variable from elif val pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds variable from elif val pattern")
val data = Some("hello")
var captured = ""
if false:
    pass
elif val Some(s) = data:
    captured = s
expect captured == "hello"
```

</details>

#### elif val with else fallback

#### falls to else when elif val does not match

- falls to else when elif val does not match


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("falls to else when elif val does not match")
var result = ""
if false:
    result = "if"
elif val Some(n) = None:
    result = "elif"
else:
    result = "else"
expect result == "else"
```

</details>

#### does not reach else when elif val matches

- does not reach else when elif val matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not reach else when elif val matches")
var result = ""
if false:
    result = "if"
elif val Some(n) = Some(99):
    result = "elif={n}"
else:
    result = "else"
expect result == "elif=99"
```

</details>

#### multiple elif val branches

#### matches first elif val pattern

- matches first elif val pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches first elif val pattern")
val a = Some(1)
val b = Some(2)
var result = ""
if false:
    result = "if"
elif val Some(n) = a:
    result = "first={n}"
elif val Some(n) = b:
    result = "second={n}"
expect result == "first=1"
```

</details>

#### matches second elif val when first does not match

- matches second elif val when first does not match


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches second elif val when first does not match")
val b = Some(2)
var result = ""
if false:
    result = "if"
elif val Some(n) = None:
    result = "first={n}"
elif val Some(n) = b:
    result = "second={n}"
expect result == "second=2"
```

</details>

#### falls through all elif val when none match

- falls through all elif val when none match


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("falls through all elif val when none match")
var result = "none"
if false:
    result = "if"
elif val Some(n) = None:
    result = "first"
elif val Some(n) = None:
    result = "second"
expect result == "none"
```

</details>

#### mixed elif and elif val

#### matches regular elif before elif val

- matches regular elif before elif val


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches regular elif before elif val")
var result = ""
if false:
    result = "if"
elif true:
    result = "elif-bool"
elif val Some(n) = Some(42):
    result = "elif-val"
expect result == "elif-bool"
```

</details>

#### matches elif val after failed regular elif

- matches elif val after failed regular elif


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches elif val after failed regular elif")
val x = Some(10)
var result = ""
if false:
    result = "if"
elif false:
    result = "elif-bool"
elif val Some(n) = x:
    result = "elif-val={n}"
expect result == "elif-val=10"
```

</details>

#### matches regular elif after failed elif val

- matches regular elif after failed elif val


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches regular elif after failed elif val")
var result = ""
if false:
    result = "if"
elif val Some(n) = None:
    result = "elif-val"
elif true:
    result = "elif-bool"
expect result == "elif-bool"
```

</details>

#### reaches else after mixed elif failures

- reaches else after mixed elif failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reaches else after mixed elif failures")
var result = ""
if false:
    result = "if"
elif false:
    result = "elif-bool"
elif val Some(n) = None:
    result = "elif-val"
else:
    result = "else"
expect result == "else"
```

</details>

#### if val combined with elif val

#### matches if val and skips elif val

- matches if val and skips elif val


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches if val and skips elif val")
var result = ""
if val Some(n) = Some(1):
    result = "if={n}"
elif val Some(n) = Some(2):
    result = "elif={n}"
expect result == "if=1"
```

</details>

#### skips if val and matches elif val

- skips if val and matches elif val


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips if val and matches elif val")
var result = ""
if val Some(n) = None:
    result = "if"
elif val Some(n) = Some(2):
    result = "elif={n}"
expect result == "elif=2"
```

</details>

#### skips both if val and elif val to else

- skips both if val and elif val to else


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips both if val and elif val to else")
var result = ""
if val Some(n) = None:
    result = "if"
elif val Some(n) = None:
    result = "elif"
else:
    result = "else"
expect result == "else"
```

</details>

#### nested option patterns

#### matches nested Some in elif val

- matches nested Some in elif val


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches nested Some in elif val")
val inner = Some(Some(99))
var result = ""
if val Some(Some(n)) = None:
    result = "none"
elif val Some(Some(n)) = inner:
    result = "nested={n}"
expect result == "nested=99"
```

</details>

#### chains multiple Some patterns

- chains multiple Some patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains multiple Some patterns")
val a = None
val b = None
val c = Some(7)
var result = ""
if val Some(x) = a:
    result = "a={x}"
elif val Some(x) = b:
    result = "b={x}"
elif val Some(x) = c:
    result = "c={x}"
else:
    result = "none"
expect result == "c=7"
```

</details>

#### elif val as implicit return

#### returns from elif val branch

- returns from elif val branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns from elif val branch")
fn classify(opt):
    if val Some(n) = None:
        "none-matched"
    elif val Some(n) = opt:
        "got={n}"
    else:
        "nothing"

expect classify(Some(7)) == "got=7"
expect classify(None) == "nothing"
```

</details>

#### elif val scope isolation

#### bindings do not leak to outer scope

- bindings do not leak to outer scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("bindings do not leak to outer scope")
var outer = "unchanged"
if val Some(n) = None:
    pass
elif val Some(n) = Some(42):
    outer = "n={n}"
# n should not be accessible here
expect outer == "n=42"
```

</details>

#### elif val with nil/no-match returns nil

#### returns nil when no branch matches

- returns nil when no branch matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns nil when no branch matches")
var result = "before"
if false:
    result = "if"
elif val Some(n) = None:
    result = "elif"
# No else - should just continue
expect result == "before"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `5783dcc41e6a48f6aef047ec14ec65c794efdf5c6ef31897e9f64c8d1a9d77df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5783dcc41e6a48f6aef047ec14ec65c794efdf5c6ef31897e9f64c8d1a9d77df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5783dcc41e6a48f6aef047ec14ec65c794efdf5c6ef31897e9f64c8d1a9d77df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/elif_val_pattern_binding_spec.spl
mirror: doc/06_spec/feature/usage/elif_val_pattern_binding_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/elif_val_pattern_binding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/elif_val_pattern_binding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/elif_val_pattern_binding_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches elif val when if condition is false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/elif_val_pattern_binding_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips elif val when pattern does not match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/elif_val_pattern_binding_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds variable from elif val pattern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
