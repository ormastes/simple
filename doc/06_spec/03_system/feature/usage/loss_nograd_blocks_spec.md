# loss{} and nograd{} Block Tests

> Purpose: evaluates addition

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# loss{} and nograd{} Block Tests

Purpose: evaluates addition

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1099-1102 (loss/nograd block support) |
| Category | Syntax / Math DSL |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/loss_nograd_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: evaluates addition
Audience: compiler and tooling engineers who maintain this spec

# loss{} and nograd{} Block Tests

**Feature IDs:** #1099-1102 (loss/nograd block support)
**Category:** Syntax / Math DSL
**Difficulty:** 2/5
**Status:** Implemented

## Overview

Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the
same supported math-expression subset as `m{}` blocks. Runtime autograd
semantics are covered by `math_autograd_runtime_spec.spl`.

## Scenarios

### loss{} block evaluation

#### basic arithmetic

#### evaluates addition

- evaluates addition
- Verify: evaluates addition
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates addition")
step("Verify: evaluates addition")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = loss{ 2 + 3 }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

</details>

#### evaluates subtraction

- evaluates subtraction
- Verify: evaluates subtraction
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates subtraction")
step("Verify: evaluates subtraction")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = loss{ 10 - 4 }
expect(result).to_equal(6)  # oracle: value fixed by the spec contract
```

</details>

#### evaluates multiplication

- evaluates multiplication
- Verify: evaluates multiplication
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates multiplication")
step("Verify: evaluates multiplication")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = loss{ 3 * 4 }
expect(result).to_equal(12)  # oracle: value fixed by the spec contract
```

</details>

#### evaluates division

- evaluates division
- Verify: evaluates division
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates division")
step("Verify: evaluates division")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = loss{ 10 / 2 }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

</details>

#### power operator

#### evaluates integer power

- evaluates integer power
- Verify: evaluates integer power
   - Expected: result equals `9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates integer power")
step("Verify: evaluates integer power")
# @req: REQ-FEATURE-LossNogrBloc-001
val x = 3.0
val result = loss{ x^2 }
expect(result).to_equal(9.0)
```

</details>

#### evaluates fractional power

- evaluates fractional power
- Verify: evaluates fractional power
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates fractional power")
step("Verify: evaluates fractional power")
# @req: REQ-FEATURE-LossNogrBloc-001
val x = 4.0
val result = loss{ x^0.5 }
expect(result).to_equal(2.0)
```

</details>

#### fractions

#### evaluates frac

- evaluates frac
- Verify: evaluates frac
   - Expected: result equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates frac")
step("Verify: evaluates frac")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = loss{ frac(1, 2) }
expect(result).to_equal(0.5)
```

</details>

#### evaluates nested frac

- evaluates nested frac
- Verify: evaluates nested frac
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates nested frac")
step("Verify: evaluates nested frac")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = loss{ frac(1, frac(1, 2)) }
expect(result).to_equal(2.0)
```

</details>

#### scope variable bridging

#### reads outer variables

- reads outer variables
- Verify: reads outer variables
   - Expected: result equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads outer variables")
step("Verify: reads outer variables")
# @req: REQ-FEATURE-LossNogrBloc-001
val x = 5.0
val y = 3.0
val result = loss{ x + y }
expect(result).to_equal(8.0)
```

</details>

#### reads multiple outer variables

- reads multiple outer variables
- Verify: reads multiple outer variables
   - Expected: result equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads multiple outer variables")
step("Verify: reads multiple outer variables")
# @req: REQ-FEATURE-LossNogrBloc-001
val a = 2.0
val b = 3.0
val c = 4.0
val result = loss{ a * b + c }
expect(result).to_equal(10.0)
```

</details>

#### math functions

#### evaluates sqrt

- evaluates sqrt
- Verify: evaluates sqrt
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates sqrt")
step("Verify: evaluates sqrt")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = loss{ sqrt(16) }
expect(result).to_equal(4.0)
```

</details>

#### evaluates exp

- evaluates exp
- Verify: evaluates exp
   - Expected: close(loss{ exp(0) }, 1.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates exp")
step("Verify: evaluates exp")
# @req: REQ-FEATURE-LossNogrBloc-001
expect(close(loss{ exp(0) }, 1.0, 0.01)).to_equal(true)
```

</details>

#### evaluates abs

- evaluates abs
- Verify: evaluates abs
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates abs")
step("Verify: evaluates abs")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = loss{ abs(-5) }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

</details>

### nograd{} block evaluation

#### basic arithmetic

#### evaluates addition

- evaluates addition
- Verify: evaluates addition
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates addition")
step("Verify: evaluates addition")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = nograd{ 2 + 3 }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

</details>

#### evaluates subtraction

- evaluates subtraction
- Verify: evaluates subtraction
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates subtraction")
step("Verify: evaluates subtraction")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = nograd{ 10 - 4 }
expect(result).to_equal(6)  # oracle: value fixed by the spec contract
```

</details>

#### evaluates multiplication

- evaluates multiplication
- Verify: evaluates multiplication
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates multiplication")
step("Verify: evaluates multiplication")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = nograd{ 3 * 4 }
expect(result).to_equal(12)  # oracle: value fixed by the spec contract
```

</details>

#### evaluates division

- evaluates division
- Verify: evaluates division
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates division")
step("Verify: evaluates division")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = nograd{ 10 / 2 }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

</details>

#### power operator

#### evaluates integer power

- evaluates integer power
- Verify: evaluates integer power
   - Expected: result equals `9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates integer power")
step("Verify: evaluates integer power")
# @req: REQ-FEATURE-LossNogrBloc-001
val x = 3.0
val result = nograd{ x^2 }
expect(result).to_equal(9.0)
```

</details>

#### evaluates fractional power

- evaluates fractional power
- Verify: evaluates fractional power
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates fractional power")
step("Verify: evaluates fractional power")
# @req: REQ-FEATURE-LossNogrBloc-001
val x = 4.0
val result = nograd{ x^0.5 }
expect(result).to_equal(2.0)
```

</details>

#### fractions

#### evaluates frac

- evaluates frac
- Verify: evaluates frac
   - Expected: result equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates frac")
step("Verify: evaluates frac")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = nograd{ frac(1, 2) }
expect(result).to_equal(0.5)
```

</details>

#### scope variable bridging

#### reads outer variables

- reads outer variables
- Verify: reads outer variables
   - Expected: result equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads outer variables")
step("Verify: reads outer variables")
# @req: REQ-FEATURE-LossNogrBloc-001
val x = 5.0
val y = 3.0
val result = nograd{ x + y }
expect(result).to_equal(8.0)
```

</details>

#### math functions

#### evaluates sqrt

- evaluates sqrt
- Verify: evaluates sqrt
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates sqrt")
step("Verify: evaluates sqrt")
# @req: REQ-FEATURE-LossNogrBloc-001
val result = nograd{ sqrt(16) }
expect(result).to_equal(4.0)
```

</details>

#### evaluates exp

- evaluates exp
- Verify: evaluates exp
   - Expected: close(nograd{ exp(0) }, 1.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates exp")
step("Verify: evaluates exp")
# @req: REQ-FEATURE-LossNogrBloc-001
expect(close(nograd{ exp(0) }, 1.0, 0.01)).to_equal(true)
```

</details>

### loss{} rendering

#### renders LaTeX via render_latex_raw

- renders LaTeX via render_latex_raw
- Verify: renders LaTeX via render_latex_raw


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders LaTeX via render_latex_raw")
step("Verify: renders LaTeX via render_latex_raw")
# @req: REQ-FEATURE-LossNogrBloc-001
val latex = render_latex_raw("frac(1, 1 + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders Unicode via to_pretty

- renders Unicode via to_pretty
- Verify: renders Unicode via to_pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders Unicode via to_pretty")
step("Verify: renders Unicode via to_pretty")
# @req: REQ-FEATURE-LossNogrBloc-001
val pretty = to_pretty("frac(1, 1 + exp(-x))")
expect(pretty).to_contain("exp")
```

</details>

### nograd{} rendering

#### renders LaTeX via render_latex_raw

- renders LaTeX via render_latex_raw
- Verify: renders LaTeX via render_latex_raw


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders LaTeX via render_latex_raw")
step("Verify: renders LaTeX via render_latex_raw")
# @req: REQ-FEATURE-LossNogrBloc-001
val latex = render_latex_raw("sqrt(frac(6, fan_in + fan_out))")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders Unicode via to_pretty

- renders Unicode via to_pretty
- Verify: renders Unicode via to_pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders Unicode via to_pretty")
step("Verify: renders Unicode via to_pretty")
# @req: REQ-FEATURE-LossNogrBloc-001
val pretty = to_pretty("sqrt(frac(6, fan_in + fan_out))")
expect(pretty).to_contain("√")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FEATURE-LossNogrBloc-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1cd4a27734ceb21b70e8c8335a67fb86ef1a194676b4ac09bbc25ae1c342367f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1cd4a27734ceb21b70e8c8335a67fb86ef1a194676b4ac09bbc25ae1c342367f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1cd4a27734ceb21b70e8c8335a67fb86ef1a194676b4ac09bbc25ae1c342367f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/loss_nograd_blocks_spec.spl
mirror: doc/06_spec/03_system/feature/usage/loss_nograd_blocks_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/loss_nograd_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/loss_nograd_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/loss_nograd_blocks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/loss_nograd_blocks_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/loss_nograd_blocks_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/loss_nograd_blocks_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
