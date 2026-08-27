# Advanced Pattern Matching Specification

> match x:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Pattern Matching Specification

match x:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PAT-ADV-001 to #PAT-ADV-018 |
| Category | Language \| Pattern Matching |
| Status | Implemented |
| Source | `test/03_system/feature/usage/pattern_matching_advanced_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Match guards
match x:
n if n > 0 => "positive"
n if n < 0 => "negative"
_ => "zero"

# If val (if let is deprecated)
if val Some(value) = opt:
print(value)

# While val (while let is deprecated)
while val Some(item) = iterator.next():
process(item)

# Or patterns
match x:
1 | 2 | 3 => "small"
_ => "large"

# Range patterns
match x:
0..10 => "single digit"
10..100 => "double digit"
_ => "large"
```

## Scenarios

### Match Guards

#### matches with basic guard

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches with basic guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches with basic guard")
fn classify(x: i64) -> i64:
    match x:
        n if n < 0 =>
            -1
        n if n == 0 =>
            0
        n if n > 0 =>
            1
    -99

expect classify(5) == 1
```

</details>

#### matches negative with guard

- matches negative with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches negative with guard")
fn classify(x: i64) -> i64:
    match x:
        n if n < 0 =>
            -1
        n if n == 0 =>
            0
        n if n > 0 =>
            1
    -99

expect classify(-10) == -1
```

</details>

#### uses binding in guard

- uses binding in guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses binding in guard")
fn verify(pair: (i64, i64)) -> i64:
    match pair:
        (a, b) if a + b > 10 =>
            1
        (a, b) if a + b == 10 =>
            0
        _ =>
            -1

expect verify((7, 5)) == 1  # 7 + 5 = 12 > 10
```

</details>

#### falls through when guard fails

- falls through when guard fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls through when guard fails")
fn test(x: i64) -> i64:
    match x:
        n if n > 100 =>
            100
        n if n > 10 =>
            10
        n =>
            n

expect test(50) == 10  # 50 > 100? No. 50 > 10? Yes
```

</details>

### If Val Expressions

#### matches Some with if val

- matches Some with if val


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches Some with if val")
val opt = Some(42)
var res = 0
if val Some(x) = opt:
    res = x
expect res == 42
```

</details>

#### uses else branch for non-matching

- uses else branch for non-matching


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses else branch for non-matching")
val opt: Option<i64> = nil
var res = 0
if val Some(x) = opt:
    res = x
else:
    res = -1
expect res == -1
```

</details>

#### matches Ok with if val

- matches Ok with if val


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches Ok with if val")
val res = Ok(100)
var output = 0
if val Ok(value) = res:
    output = value
expect output == 100
```

</details>

#### matches Some with if var

- matches Some with if var


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches Some with if var")
val opt = Some(42)
var res = 0
if var Some(x) = opt:
    res = x
expect res == 42
```

</details>

### While Let Expressions

<details>
<summary>Advanced: loops while pattern matches</summary>

#### loops while pattern matches

- loops while pattern matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loops while pattern matches")
fn next_item(n: i64) -> Option<i64>:
    if n > 0:
        Some(n)
    else:
        None

var counter = 3
var sum = 0
while let Some(value) = next_item(counter):
    sum = sum + value
    counter = counter - 1
expect sum == 6  # 3 + 2 + 1
```

</details>


</details>

### Or Patterns

#### matches multiple literals

- matches multiple literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches multiple literals")
fn classify(x: i64) -> i64:
    match x:
        1 | 2 | 3 =>
            1  # small
        4 | 5 | 6 =>
            2  # medium
        _ =>
            3  # large

expect classify(2) == 1
```

</details>

#### matches medium group

- matches medium group


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches medium group")
fn classify(x: i64) -> i64:
    match x:
        1 | 2 | 3 =>
            1
        4 | 5 | 6 =>
            2
        _ =>
            3

expect classify(5) == 2
```

</details>

#### falls through to wildcard

- falls through to wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls through to wildcard")
fn verify(x: i64) -> i64:
    match x:
        0 | 1 =>
            10
        _ =>
            99

expect verify(99) == 99
```

</details>

### Range Patterns

#### matches exclusive range

- matches exclusive range


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches exclusive range")
fn classify(x: i64) -> i64:
    match x:
        0..10 =>
            1
        10..20 =>
            2
        _ =>
            3

expect classify(5) == 1
```

</details>

#### exclusive range excludes end

- exclusive range excludes end


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exclusive range excludes end")
fn classify(x: i64) -> i64:
    match x:
        0..10 =>
            1
        10..20 =>
            2
        _ =>
            3

expect classify(10) == 2  # 10 not in 0..10
```

</details>

#### matches inclusive range

- matches inclusive range


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches inclusive range")
fn classify(x: i64) -> i64:
    match x:
        0..=5 =>
            1
        6..=10 =>
            2
        _ =>
            3

expect classify(5) == 1  # 5 is in 0..=5
```

</details>

### Numeric Literals

#### parses hex literal

- parses hex literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses hex literal")
val x = 0xFF
expect x == 255
```

</details>

#### hex arithmetic

- hex arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hex arithmetic")
val x = 0x10 + 0x20
expect x == 48  # 16 + 32
```

</details>

#### parses binary literal

- parses binary literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses binary literal")
val x = 0b1010
expect x == 10
```

</details>

#### binary with underscores

- binary with underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binary with underscores")
val x = 0b1111_0000
expect x == 240
```

</details>

#### parses octal literal

- parses octal literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses octal literal")
val x = 0o755
expect x == 493  # 7*64 + 5*8 + 5
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ecda821eb20be3b7b88e21c5ddf818bd090d8d1f651dfffa520363e3b5491deb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecda821eb20be3b7b88e21c5ddf818bd090d8d1f651dfffa520363e3b5491deb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecda821eb20be3b7b88e21c5ddf818bd090d8d1f651dfffa520363e3b5491deb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/pattern_matching_advanced_spec.spl
mirror: doc/06_spec/03_system/feature/usage/pattern_matching_advanced_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/pattern_matching_advanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/pattern_matching_advanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/pattern_matching_advanced_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches with basic guard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/pattern_matching_advanced_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches negative with guard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/pattern_matching_advanced_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses binding in guard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
