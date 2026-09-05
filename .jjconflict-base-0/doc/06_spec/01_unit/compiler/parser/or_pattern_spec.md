# Or Pattern Specification

> Tests covering or-patterns in match.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Or Pattern Specification

## Scenarios

### or-patterns in match

#### matches first alternative

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches first alternative
   - Expected: result equals `small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches first alternative")
val x = 1
val result = match x:
    case 1 | 2 | 3: "small"
    case _: "other"
expect(result).to_equal("small")
```

</details>

#### matches second alternative

- matches second alternative
   - Expected: result equals `small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches second alternative")
val x = 2
val result = match x:
    case 1 | 2 | 3: "small"
    case _: "other"
expect(result).to_equal("small")
```

</details>

#### matches third alternative

- matches third alternative
   - Expected: result equals `small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches third alternative")
val x = 3
val result = match x:
    case 1 | 2 | 3: "small"
    case _: "other"
expect(result).to_equal("small")
```

</details>

#### falls through to wildcard when no alternative matches

- falls through to wildcard when no alternative matches
   - Expected: result equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls through to wildcard when no alternative matches")
val x = 99
val result = match x:
    case 1 | 2 | 3: "small"
    case _: "other"
expect(result).to_equal("other")
```

</details>

#### or-pattern on text

- or-pattern on text
   - Expected: result equals `affirmative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or-pattern on text")
val s = "yes"
val result = match s:
    case "yes" | "y" | "true": "affirmative"
    case "no" | "n" | "false": "negative"
    case _: "unknown"
expect(result).to_equal("affirmative")
```

</details>

#### or-pattern on text second branch

- or-pattern on text second branch
   - Expected: result equals `negative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or-pattern on text second branch")
val s = "n"
val result = match s:
    case "yes" | "y" | "true": "affirmative"
    case "no" | "n" | "false": "negative"
    case _: "unknown"
expect(result).to_equal("negative")
```

</details>

#### two-way or-pattern

- two-way or-pattern
   - Expected: result equals `magic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two-way or-pattern")
val n = 7
val result = match n:
    case 7 | 42: "magic"
    case _: "mundane"
expect(result).to_equal("magic")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/or_pattern_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering or-patterns in match.
- or-patterns in match

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee3a411421079e2987a550cc21102a8278d38d02744088a275d85d35967ce19c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee3a411421079e2987a550cc21102a8278d38d02744088a275d85d35967ce19c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee3a411421079e2987a550cc21102a8278d38d02744088a275d85d35967ce19c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/or_pattern_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/or_pattern_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/or_pattern_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/or_pattern_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/or_pattern_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches first alternative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/or_pattern_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches second alternative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/or_pattern_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches third alternative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
