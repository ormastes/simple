# Inlining Specification

> Tests covering Simple Function Inlining, Branching Function Inlining, Multi-branch Inlining, Nested Call Inlining.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inlining Specification

## Scenarios

### Simple Function Inlining

#### inline identity function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- inline identity function


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline identity function")
check(identity(42) == 42)
```

</details>

#### inline add_one function

- inline add_one function


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline add_one function")
check(add_one(41) == 42)
```

</details>

#### inline with zero

- inline with zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline with zero")
check(add_one(0) == 1)
```

</details>

#### inline with negative

- inline with negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline with negative")
check(add_one(-1) == 0)
```

</details>

### Branching Function Inlining

#### inline max - first larger

- inline max - first larger


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline max - first larger")
check(max_val(10, 5) == 10)
```

</details>

#### inline max - second larger

- inline max - second larger


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline max - second larger")
check(max_val(5, 10) == 10)
```

</details>

#### inline max - equal

- inline max - equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline max - equal")
check(max_val(5, 5) == 5)
```

</details>

#### inline min - first smaller

- inline min - first smaller


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline min - first smaller")
check(min_val(3, 7) == 3)
```

</details>

#### inline min - second smaller

- inline min - second smaller


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline min - second smaller")
check(min_val(7, 3) == 3)
```

</details>

#### inline abs - positive

- inline abs - positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline abs - positive")
check(abs_val(5) == 5)
```

</details>

#### inline abs - negative

- inline abs - negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline abs - negative")
check(abs_val(-5) == 5)
```

</details>

#### inline abs - zero

- inline abs - zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline abs - zero")
check(abs_val(0) == 0)
```

</details>

### Multi-branch Inlining

#### clamp within range

- clamp within range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamp within range")
check(clamp(5, 0, 10) == 5)
```

</details>

#### clamp below minimum

- clamp below minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamp below minimum")
check(clamp(-5, 0, 10) == 0)
```

</details>

#### clamp above maximum

- clamp above maximum


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamp above maximum")
check(clamp(15, 0, 10) == 10)
```

</details>

#### clamp at minimum

- clamp at minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamp at minimum")
check(clamp(0, 0, 10) == 0)
```

</details>

#### clamp at maximum

- clamp at maximum


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamp at maximum")
check(clamp(10, 0, 10) == 10)
```

</details>

### Nested Call Inlining

#### inline nested calls

- inline nested calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline nested calls")
check(add_one(add_one(40)) == 42)
```

</details>

#### inline max of add_one

- inline max of add_one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline max of add_one")
check(max_val(add_one(5), add_one(3)) == 6)
```

</details>

#### inline chained operations

- inline chained operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inline chained operations")
val result = abs_val(min_val(-3, -5))
check(result == 5)
```

</details>

#### deeply nested inlining

- deeply nested inlining


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deeply nested inlining")
check(add_one(add_one(add_one(add_one(0)))) == 4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mir_opt/inlining_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Function Inlining, Branching Function Inlining, Multi-branch Inlining, Nested Call Inlining.
- Simple Function Inlining
- Branching Function Inlining
- Multi-branch Inlining
- Nested Call Inlining

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `6cb633db998a24475446f211c33d2f926e35466e996e831555b2879d76f663be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6cb633db998a24475446f211c33d2f926e35466e996e831555b2879d76f663be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6cb633db998a24475446f211c33d2f926e35466e996e831555b2879d76f663be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/mir_opt/inlining_spec.spl
mirror: doc/06_spec/unit/compiler/mir_opt/inlining_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mir_opt/inlining_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir_opt/inlining_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir_opt/inlining_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inline identity function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/inlining_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inline add_one function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/inlining_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inline with zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
