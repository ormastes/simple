# Default Arguments Specification

> Tests for function default argument values.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Default Arguments Specification

Tests for function default argument values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DEFARG-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/feature/usage/default_arguments_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for function default argument values.

## Syntax

```simple
use std.spec.step

fn greet(name, greeting="Hello"):
print "{greeting}, {name}!"

greet("Alice")           # Uses default: "Hello, Alice!"
greet("Bob", "Hi")       # Override: "Hi, Bob!"
```

## Scenarios

### Default Arguments

#### uses default argument when not provided

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses default argument when not provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses default argument when not provided")
fn add(a, b=10):
    return a + b

expect add(5) == 15
```

</details>

#### overrides default argument when provided

- overrides default argument when provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("overrides default argument when provided")
fn add(a, b=10):
    return a + b

expect add(5, b=20) == 25
```

</details>

#### uses multiple default arguments

- uses multiple default arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses multiple default arguments")
fn calc(a, b=2, c=3):
    return a + b * c

expect calc(1) == 7
```

</details>

#### overrides some default arguments

- overrides some default arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("overrides some default arguments")
fn calc(a, b=2, c=3):
    return a + b * c

expect calc(1, c=10) == 21
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `da9cc666c0f199171b77a184517b764f01e98fc59561397d5dbba4bd0d399ab7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da9cc666c0f199171b77a184517b764f01e98fc59561397d5dbba4bd0d399ab7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da9cc666c0f199171b77a184517b764f01e98fc59561397d5dbba4bd0d399ab7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/default_arguments_spec.spl
mirror: doc/06_spec/feature/usage/default_arguments_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/default_arguments_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/default_arguments_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/default_arguments_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses default argument when not provided' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/default_arguments_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overrides default argument when provided' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/default_arguments_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses multiple default arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
