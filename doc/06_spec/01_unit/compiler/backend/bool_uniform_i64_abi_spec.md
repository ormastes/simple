# Bool Uniform I64 Abi Specification

> Tests covering bool returned directly from a comparison, bool passed through a call chain, not applied to a call-boundary-crossed comparison result, bool stored in a var then used to branch, bool params combined with and/or across call boundaries, bool-driven loop counting across a call boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bool Uniform I64 Abi Specification

## Scenarios

### bool returned directly from a comparison

#### returns true for a satisfying comparison

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns true for a satisfying comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for a satisfying comparison")
check(is_even(4) == true)
```

</details>

#### returns false for a failing comparison

- returns false for a failing comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for a failing comparison")
check(is_even(5) == false)
```

</details>

#### round-trips through a boolean variable before being asserted

- round-trips through a boolean variable before being asserted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips through a boolean variable before being asserted")
val result = is_even(4)
check(result == true)
```

</details>

### bool passed through a call chain

#### preserves true through a single pass-through call

- preserves true through a single pass-through call


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves true through a single pass-through call")
check(pass_through(is_even(4)) == true)
```

</details>

#### preserves false through a single pass-through call

- preserves false through a single pass-through call


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves false through a single pass-through call")
check(pass_through(is_even(5)) == false)
```

</details>

#### preserves true through a three-deep call chain

- preserves true through a three-deep call chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves true through a three-deep call chain")
check(pass_through(pass_through(pass_through(is_even(10)))) == true)
```

</details>

#### preserves false through a three-deep call chain

- preserves false through a three-deep call chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves false through a three-deep call chain")
check(pass_through(pass_through(pass_through(is_even(11)))) == false)
```

</details>

### not applied to a call-boundary-crossed comparison result

#### inverts a true comparison result carried across a call boundary

- inverts a true comparison result carried across a call boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inverts a true comparison result carried across a call boundary")
check(negate(pass_through(is_even(4))) == false)
```

</details>

#### inverts a false comparison result carried across a call boundary

- inverts a false comparison result carried across a call boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inverts a false comparison result carried across a call boundary")
check(negate(pass_through(is_even(5))) == true)
```

</details>

#### double negation restores the original value after two call boundaries

- double negation restores the original value after two call boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("double negation restores the original value after two call boundaries")
check(negate(negate(pass_through(is_even(4)))) == true)
```

</details>

### bool stored in a var then used to branch

#### takes the true branch when the stored comparison result is true

- takes the true branch when the stored comparison result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the true branch when the stored comparison result is true")
var flag = is_even(10)
var branch_taken = ""
if flag:
    branch_taken = "true"
else:
    branch_taken = "false"
check(branch_taken == "true")
```

</details>

#### takes the false branch when the stored comparison result is false

- takes the false branch when the stored comparison result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the false branch when the stored comparison result is false")
var flag = is_even(11)
var branch_taken = ""
if flag:
    branch_taken = "true"
else:
    branch_taken = "false"
check(branch_taken == "false")
```

</details>

#### branches correctly on a bool that traveled through a call boundary

- branches correctly on a bool that traveled through a call boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("branches correctly on a bool that traveled through a call boundary")
var flag = pass_through(is_even(4))
var branch_taken = ""
if flag:
    branch_taken = "true"
else:
    branch_taken = "false"
check(branch_taken == "true")
```

</details>

### bool params combined with and/or across call boundaries

#### and_both is true only when both call-boundary-crossed comparisons are true

- and_both is true only when both call-boundary-crossed comparisons are true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and_both is true only when both call-boundary-crossed comparisons are true")
check(and_both(is_even(4), is_even(6)) == true)
check(and_both(is_even(4), is_even(5)) == false)
check(and_both(is_even(3), is_even(5)) == false)
```

</details>

#### or_both is false only when both call-boundary-crossed comparisons are false

- or_both is false only when both call-boundary-crossed comparisons are false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or_both is false only when both call-boundary-crossed comparisons are false")
check(or_both(is_even(3), is_even(5)) == false)
check(or_both(is_even(4), is_even(5)) == true)
check(or_both(is_even(4), is_even(6)) == true)
```

</details>

### bool-driven loop counting across a call boundary

#### counts exactly the values matching a call-boundary-crossed predicate

- counts exactly the values matching a call-boundary-crossed predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts exactly the values matching a call-boundary-crossed predicate")
var count = 0
for i in 0..20:
    if pass_through(is_even(i)) and not pass_through(is_even(i + 1)):
        count = count + 1
check(count == 10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/bool_uniform_i64_abi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bool returned directly from a comparison, bool passed through a call chain, not applied to a call-boundary-crossed comparison result, bool stored in a var then used to branch, bool params combined with and/or across call boundaries, bool-driven loop counting across a call boundary.
- bool returned directly from a comparison
- bool passed through a call chain
- not applied to a call-boundary-crossed comparison result
- bool stored in a var then used to branch
- bool params combined with and/or across call boundaries
- bool-driven loop counting across a call boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `bc8725a110bde8df9ad496b81bf8d3f52ae2df6c476239ade20f206723724272`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc8725a110bde8df9ad496b81bf8d3f52ae2df6c476239ade20f206723724272`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc8725a110bde8df9ad496b81bf8d3f52ae2df6c476239ade20f206723724272`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/bool_uniform_i64_abi_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/bool_uniform_i64_abi_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/bool_uniform_i64_abi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/bool_uniform_i64_abi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/bool_uniform_i64_abi_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true for a satisfying comparison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/bool_uniform_i64_abi_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for a failing comparison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/bool_uniform_i64_abi_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips through a boolean variable before being asserted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
