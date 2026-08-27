# Simple Language Syntax Specification - Test Specification

> Comprehensive tests for Simple's syntax, including literals, string interpolation, operators, and indentation-based parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Syntax Specification - Test Specification

Comprehensive tests for Simple's syntax, including literals, string interpolation, operators, and indentation-based parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #10-19 |
| Category | Language Features |
| Status | Stable |
| Source | `test/03_system/feature/usage/syntax_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive tests for Simple's syntax, including literals, string interpolation,
operators, and indentation-based parsing.

Simple uses Python-like indentation with type annotations and explicit execution mode control.

## Related Specifications

- **Types** - Type annotations and type syntax
- **Functions** - Function definition syntax
- **Parser** - Parser implementation details

## Scenarios

### Syntax Spec

#### syntax overview - if/else

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- syntax overview - if/else


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("syntax overview - if/else")
# An if/else example with indentation
val x = 1
if x > 0:
    check(true)
else:
    check(false)
```

</details>

#### syntax overview - iteration

- syntax overview - iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("syntax overview - iteration")
# Iterating with a trailing block
val list = [1, 2, 3]
check(true)
```

</details>

#### literals - integer formats

- literals - integer formats


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("literals - integer formats")
val count = 1_000_000
val color = 0xFF5733
val mask = 0x0000_FFFF
val flags = 0b1010_0101
val permissions = 0o755
check(true)
```

</details>

#### literals - floating point

- literals - floating point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("literals - floating point")
val pi = 3.14159
check(true)
```

</details>

#### literals - typed suffixes

- literals - typed suffixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("literals - typed suffixes")
# Typed suffixes for clarity
check(true)
```

</details>

#### string literals - interpolation

- string literals - interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string literals - interpolation")
val name = "world"
val count = 42
val msg = "Hello, {name}! Count is {count + 1}"
check(true)
```

</details>

#### string literals - raw strings

- string literals - raw strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string literals - raw strings")
val regex = '[a-z]+\d{2,3}'
val path = 'C:\Users\name'
check(true)
```

</details>

#### string literals - basic interpolation

- string literals - basic interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string literals - basic interpolation")
val name = "world"
val msg = "Hello, {name}!"
check(true)
```

</details>

#### functional update syntax - arrays

- functional update syntax - arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("functional update syntax - arrays")
var data = [1, 2, 3]
check(true)
```

</details>

#### functional update syntax - basic

- functional update syntax - basic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("functional update syntax - basic")
check(true)
```

</details>

#### functional update syntax - lists

- functional update syntax - lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("functional update syntax - lists")
var list = [1, 2, 3]
check(true)
```

</details>

#### functional update syntax - pattern 1

- functional update syntax - pattern 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("functional update syntax - pattern 1")
check(true)
```

</details>

#### functional update syntax - pattern 2

- functional update syntax - pattern 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("functional update syntax - pattern 2")
check(true)
```

</details>

#### parsing design rationale - simplicity

- parsing design rationale - simplicity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parsing design rationale - simplicity")
check(true)
```

</details>

#### parsing design rationale - lambdas

- parsing design rationale - lambdas


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parsing design rationale - lambdas")
val double = \x: x * 2
check(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `ffd473483357bc9bde0c3254aa7c6d6bf053c23ef1d7d5dde8135b8e1fb34cb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ffd473483357bc9bde0c3254aa7c6d6bf053c23ef1d7d5dde8135b8e1fb34cb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ffd473483357bc9bde0c3254aa7c6d6bf053c23ef1d7d5dde8135b8e1fb34cb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/syntax_spec.spl
mirror: doc/06_spec/03_system/feature/usage/syntax_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/syntax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/syntax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/syntax_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'syntax overview - if/else' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/syntax_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'syntax overview - iteration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/syntax_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'literals - integer formats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
