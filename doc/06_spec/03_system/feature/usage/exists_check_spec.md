# Existence Check Operator (.?) Specification

> The `.?` operator checks if a value is "present" (non-nil AND non-empty). Returns `T?` — the value itself if present, `nil` if absent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Existence Check Operator (.?) Specification

The `.?` operator checks if a value is "present" (non-nil AND non-empty). Returns `T?` — the value itself if present, `nil` if absent.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2100 |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | Implemented |
| Research | doc/01_research/text_validity_presence_pattern_2026-02-24.md |
| Source | `test/03_system/feature/usage/exists_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `.?` operator checks if a value is "present" (non-nil AND non-empty).
Returns `T?` — the value itself if present, `nil` if absent.

After compiler rebuild, `.?` returns `T?` instead of `bool`, enabling
pattern binding (`if val x = expr.?:`) and nil coalescing (`expr.? ?? default`).

## Behavior

- Option types: pass-through (Some stays Some, nil stays nil)
- Collections: returns value if non-empty, nil if empty
- Strings: returns value if non-empty, nil if ""
- Primitives: always returns value (0, false are still present)

## Related

- `presence(text) -> text?` — named equivalent for text
- `presence_trimmed(text) -> text?` — blank-aware variant

## Scenarios

### Existence Check Operator .?

#### Option type

#### returns true for Some

- returns true for Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for Some")
val some_val: Option<i32> = Some(42)
expect some_val != nil
```

</details>

#### returns true for Some(0)

- returns true for Some(0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for Some(0)")
val some_zero: Option<i32> = Some(0)
expect some_zero != nil
```

</details>

#### returns false for None

- returns false for None


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for None")
val none_val: Option<i32> = None
expect none_val == nil
```

</details>

#### List type

#### returns false for empty list

- returns false for empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for empty list")
val empty: List<i32> = []
expect empty == nil
```

</details>

#### returns true for non-empty list

- returns true for non-empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for non-empty list")
val items = [1, 2, 3]
expect items != nil
```

</details>

#### Dict type

#### returns false for empty dict

- returns false for empty dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for empty dict")
val empty: Dict<text, i32> = {}
expect empty == nil
```

</details>

#### returns true for non-empty dict

- returns true for non-empty dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for non-empty dict")
val items = {"a": 1}
expect items != nil
```

</details>

#### String type

#### returns false for empty string

- returns false for empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for empty string")
val empty = ""
expect empty == nil
```

</details>

#### returns true for non-empty string

- returns true for non-empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for non-empty string")
val s = "hello"
expect s != nil
```

</details>

#### Primitive types

#### returns true for positive number

- returns true for positive number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for positive number")
val num = 42
expect num != nil
```

</details>

#### returns true for zero

- returns true for zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for zero")
val zero = 0
expect zero != nil
```

</details>

#### returns true for false

- returns true for false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for false")
val flag = false
expect flag != nil
```

</details>

#### with no-paren method calls

#### works with list.first.?

- works with list.first.?


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with list.first.?")
val items = [1, 2, 3]
expect items.first != nil
```

</details>

#### returns false for empty list.first.?

- returns false for empty list.first.?


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for empty list.first.?")
val empty: List<i32> = []
expect empty.first == nil
```

</details>

#### works with string.trim.?

- works with string.trim.?


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with string.trim.?")
val s = "  hello  "
expect s.trim != nil
```

</details>

#### works with chained no-paren methods

- works with chained no-paren methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with chained no-paren methods")
val s = "  HELLO  "
expect s.trim.lower != nil
```

</details>

#### returns false for empty result

- returns false for empty result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for empty result")
val empty = ""
expect empty.trim == nil
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/01_research/text_validity_presence_pattern_2026-02-24.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c7cd411491961e64ff5590357108b424997d13fc1b7bd34653cf672017e71a55`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7cd411491961e64ff5590357108b424997d13fc1b7bd34653cf672017e71a55`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7cd411491961e64ff5590357108b424997d13fc1b7bd34653cf672017e71a55`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/exists_check_spec.spl
mirror: doc/06_spec/03_system/feature/usage/exists_check_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/exists_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/exists_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/exists_check_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true for Some' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/exists_check_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true for Some(0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/exists_check_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for None' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
