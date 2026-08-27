# Guard Clause Specification

> match value:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guard Clause Specification

match value:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUARD-CLAUSE |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/guard_clause_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
match value:
case pattern if condition:
body
```

## Key Behaviors

- Guard conditions are evaluated after pattern matching succeeds
- Variables bound in the pattern are available in the guard condition
- If the guard evaluates to false, matching continues to the next arm
- Guards can reference external variables from the enclosing scope

## Scenarios

### Guard Clauses

#### basic integer guards

#### matches when guard is true

- matches when guard is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches when guard is true")
fn classify(x: i64) -> text:
    match x:
        case n if n > 10:
            "large"
        case n if n > 0:
            "small"
        case _:
            "non-positive"
expect classify(15) == "large"
```

</details>

#### falls through when guard is false

- falls through when guard is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("falls through when guard is false")
fn classify(x: i64) -> text:
    match x:
        case n if n > 10:
            "large"
        case n if n > 0:
            "small"
        case _:
            "non-positive"
expect classify(5) == "small"
```

</details>

#### reaches default case when all guards fail

- reaches default case when all guards fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reaches default case when all guards fail")
fn classify(x: i64) -> text:
    match x:
        case n if n > 10:
            "large"
        case n if n > 0:
            "small"
        case _:
            "non-positive"
expect classify(-5) == "non-positive"
```

</details>

#### guards with equality checks

#### matches exact value via guard

- matches exact value via guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches exact value via guard")
fn identify(x: i64) -> text:
    match x:
        case n if n == 0:
            "zero"
        case n if n == 42:
            "answer"
        case _:
            "other"
expect identify(0) == "zero"
expect identify(42) == "answer"
expect identify(99) == "other"
```

</details>

#### guards with tuple patterns

#### uses bound variables in guard

- uses bound variables in guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses bound variables in guard")
fn check_sum(pair: (i64, i64)) -> text:
    match pair:
        case (a, b) if a + b > 100:
            "big sum"
        case (a, b) if a == b:
            "equal"
        case _:
            "other"
expect check_sum((60, 50)) == "big sum"
expect check_sum((5, 5)) == "equal"
expect check_sum((1, 2)) == "other"
```

</details>

#### guards with multiple comparisons

- guards with multiple comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("guards with multiple comparisons")
fn check_range(pair: (i64, i64)) -> text:
    match pair:
        case (a, b) if a > 0 && b > 0:
            "both positive"
        case (a, b) if a < 0 && b < 0:
            "both negative"
        case _:
            "mixed"
expect check_range((5, 10)) == "both positive"
expect check_range((-5, -10)) == "both negative"
expect check_range((5, -10)) == "mixed"
```

</details>

#### guards with enum patterns

#### filters enum payload with guard

- filters enum payload with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("filters enum payload with guard")
fn categorize(v: GuardValue) -> text:
    match v:
        case GuardValue.Num(n) if n > 100:
            "large number"
        case GuardValue.Num(n) if n > 0:
            "small number"
        case GuardValue.Num(n):
            "non-positive"
        case GuardValue.Empty:
            "empty"
expect categorize(GuardValue.Num(200)) == "large number"
expect categorize(GuardValue.Num(50)) == "small number"
expect categorize(GuardValue.Num(-5)) == "non-positive"
expect categorize(GuardValue.Empty) == "empty"
```

</details>

#### guards with external variables

#### references variables from outer scope

- references variables from outer scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("references variables from outer scope")
fn above_threshold(x: i64, threshold: i64) -> bool:
    match x:
        case n if n > threshold:
            true
        case _:
            false
expect above_threshold(75, 50) == true
expect above_threshold(25, 50) == false
```

</details>

#### guards with complex expressions

#### uses modulo in guard

- uses modulo in guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses modulo in guard")
fn parity(x: i64) -> text:
    match x:
        case n if n % 2 == 0:
            "even"
        case _:
            "odd"
expect parity(10) == "even"
expect parity(7) == "odd"
```

</details>

#### uses logical or in guard

- uses logical or in guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses logical or in guard")
fn is_special(x: i64) -> bool:
    match x:
        case n if n == 1 || n == 42 || n == 100:
            true
        case _:
            false
expect is_special(1) == true
expect is_special(42) == true
expect is_special(100) == true
expect is_special(50) == false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `71fd46a11cada3e3f56fccaedd27048ec9f6c6ed7c9251a7012c81102275542c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71fd46a11cada3e3f56fccaedd27048ec9f6c6ed7c9251a7012c81102275542c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71fd46a11cada3e3f56fccaedd27048ec9f6c6ed7c9251a7012c81102275542c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/guard_clause_spec.spl
mirror: doc/06_spec/feature/usage/guard_clause_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/guard_clause_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/guard_clause_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/guard_clause_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches when guard is true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/guard_clause_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls through when guard is false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/guard_clause_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaches default case when all guards fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
