# Pattern Matching Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Matching Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PATTERN-MATCH |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/pattern_matching_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Behaviors

- Pattern matching deconstructs values into their components
- Variables bound in patterns are available in match arm bodies
- Patterns include literals, enums, tuples, records, and wildcards

## Scenarios

### Basic Pattern Matching

#### matches exact literal values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches exact literal values


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches exact literal values")
fn classify(x):
    match x:
        0 =>
            return 0
        1 =>
            return 1
        _ =>
            return 99
expect classify(0) == 0
expect classify(1) == 1
expect classify(42) == 99
```

</details>

#### matches with wildcard pattern

- matches with wildcard pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches with wildcard pattern")
fn always_match(x):
    match x:
        _ =>
            return 42
expect always_match(100) == 42
expect always_match(-1) == 42
```

</details>

#### binds value to variable

- binds value to variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds value to variable")
fn double_it(x):
    match x:
        n =>
            return n * 2
expect double_it(5) == 10
expect double_it(0) == 0
```

</details>

### Tuple Pattern Matching

#### matches tuple and extracts elements

- matches tuple and extracts elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches tuple and extracts elements")
fn sum_pair(pair):
    match pair:
        (a, b) =>
            return a + b
expect sum_pair((10, 20)) == 30
```

</details>

#### matches nested tuples

- matches nested tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches nested tuples")
fn extract_first(nested):
    match nested:
        ((a, _), _) =>
            return a
expect extract_first(((5, 10), 20)) == 5
```

</details>

#### matches with partial wildcard

- matches with partial wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches with partial wildcard")
fn get_first(pair):
    match pair:
        (x, _) =>
            return x
expect get_first((42, 100)) == 42
```

</details>

### Enum Pattern Matching

#### matches Option Some variant

- matches Option Some variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches Option Some variant")
val opt = Some(42)
var result = 0
match opt:
    Some(x) =>
        result = x
    None =>
        result = -1
expect result == 42
```

</details>

#### matches Option None variant

- matches Option None variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches Option None variant")
val opt = nil
var result = 0
match opt:
    Some(x) =>
        result = x
    None =>
        result = -1
expect result == -1
```

</details>

#### matches Result Ok variant

- matches Result Ok variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches Result Ok variant")
val res = Ok(100)
var result = 0
match res:
    Ok(x) =>
        result = x
    Err(_) =>
        result = -1
expect result == 100
```

</details>

### Pattern Matching in Functions

#### uses match as expression

- uses match as expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses match as expression")
fn sign(x):
    return match x:
        n if n > 0 =>
            1
        n if n < 0 =>
            -1
        _ =>
            0
expect sign(10) == 1
expect sign(-5) == -1
expect sign(0) == 0
```

</details>

#### matches multiple patterns

- matches multiple patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches multiple patterns")
fn is_special(x):
    match x:
        0 =>
            return true
        1 =>
            return true
        _ =>
            return false
expect is_special(0) == true
expect is_special(1) == true
expect is_special(5) == false
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

- Canonical SPipe generation for source `bdbaf6f39c24a37494ad9e4eafc49cb1c95327c16f960cc3069ae6bb2fd97472`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bdbaf6f39c24a37494ad9e4eafc49cb1c95327c16f960cc3069ae6bb2fd97472`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bdbaf6f39c24a37494ad9e4eafc49cb1c95327c16f960cc3069ae6bb2fd97472`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/pattern_matching_spec.spl
mirror: doc/06_spec/feature/usage/pattern_matching_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/pattern_matching_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/pattern_matching_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/pattern_matching_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches exact literal values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/pattern_matching_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches with wildcard pattern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/pattern_matching_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds value to variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
