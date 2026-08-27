# loss{} and nograd{} Block Tests

> Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the same supported math-expression subset as `m{}` blocks. Runtime autograd semantics are covered by `math_autograd_runtime_spec.spl`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# loss{} and nograd{} Block Tests

Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the same supported math-expression subset as `m{}` blocks. Runtime autograd semantics are covered by `math_autograd_runtime_spec.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1099-1102 (loss/nograd block support) |
| Category | Syntax / Math DSL |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/loss_nograd_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the
same supported math-expression subset as `m{}` blocks. Runtime autograd
semantics are covered by `math_autograd_runtime_spec.spl`.

## Scenarios

### loss{} block evaluation

#### basic arithmetic

#### evaluates addition

- evaluates addition
- evaluates addition
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates addition")
step("evaluates addition")
# @req: REQ-FEAT-USAGE-LOSS-NOGRAD-BLOCKS-SPEC-001
val result = loss{ 2 + 3 }
expect(result).to_equal(5)
```

</details>

#### evaluates subtraction

- evaluates subtraction
- evaluates subtraction
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates subtraction")
step("evaluates subtraction")
val result = loss{ 10 - 4 }
expect(result).to_equal(6)
```

</details>

#### evaluates multiplication

- evaluates multiplication
- evaluates multiplication
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates multiplication")
step("evaluates multiplication")
val result = loss{ 3 * 4 }
expect(result).to_equal(12)
```

</details>

#### evaluates division

- evaluates division
- evaluates division
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates division")
step("evaluates division")
val result = loss{ 10 / 2 }
expect(result).to_equal(5)
```

</details>

#### power operator

#### evaluates integer power

- evaluates integer power
- evaluates integer power
   - Expected: result equals `9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates integer power")
step("evaluates integer power")
val x = 3.0
val result = loss{ x^2 }
expect(result).to_equal(9.0)
```

</details>

#### evaluates fractional power

- evaluates fractional power
- evaluates fractional power
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates fractional power")
step("evaluates fractional power")
val x = 4.0
val result = loss{ x^0.5 }
expect(result).to_equal(2.0)
```

</details>

#### fractions

#### evaluates frac

- evaluates frac
- evaluates frac
   - Expected: result equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates frac")
step("evaluates frac")
val result = loss{ frac(1, 2) }
expect(result).to_equal(0.5)
```

</details>

#### evaluates nested frac

- evaluates nested frac
- evaluates nested frac
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates nested frac")
step("evaluates nested frac")
val result = loss{ frac(1, frac(1, 2)) }
expect(result).to_equal(2.0)
```

</details>

#### scope variable bridging

#### reads outer variables

- reads outer variables
- reads outer variables
   - Expected: result equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reads outer variables")
step("reads outer variables")
val x = 5.0
val y = 3.0
val result = loss{ x + y }
expect(result).to_equal(8.0)
```

</details>

#### reads multiple outer variables

- reads multiple outer variables
- reads multiple outer variables
   - Expected: result equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reads multiple outer variables")
step("reads multiple outer variables")
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
- evaluates sqrt
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates sqrt")
step("evaluates sqrt")
val result = loss{ sqrt(16) }
expect(result).to_equal(4.0)
```

</details>

#### evaluates exp

- evaluates exp
- evaluates exp
   - Expected: close(loss{ exp(0) }, 1.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates exp")
step("evaluates exp")
expect(close(loss{ exp(0) }, 1.0, 0.01)).to_equal(true)
```

</details>

#### evaluates abs

- evaluates abs
- evaluates abs
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates abs")
step("evaluates abs")
val result = loss{ abs(-5) }
expect(result).to_equal(5)
```

</details>

### nograd{} block evaluation

#### basic arithmetic

#### evaluates addition

- evaluates addition
- evaluates addition
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates addition")
step("evaluates addition")
val result = nograd{ 2 + 3 }
expect(result).to_equal(5)
```

</details>

#### evaluates subtraction

- evaluates subtraction
- evaluates subtraction
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates subtraction")
step("evaluates subtraction")
val result = nograd{ 10 - 4 }
expect(result).to_equal(6)
```

</details>

#### evaluates multiplication

- evaluates multiplication
- evaluates multiplication
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates multiplication")
step("evaluates multiplication")
val result = nograd{ 3 * 4 }
expect(result).to_equal(12)
```

</details>

#### evaluates division

- evaluates division
- evaluates division
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates division")
step("evaluates division")
val result = nograd{ 10 / 2 }
expect(result).to_equal(5)
```

</details>

#### power operator

#### evaluates integer power

- evaluates integer power
- evaluates integer power
   - Expected: result equals `9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates integer power")
step("evaluates integer power")
val x = 3.0
val result = nograd{ x^2 }
expect(result).to_equal(9.0)
```

</details>

#### evaluates fractional power

- evaluates fractional power
- evaluates fractional power
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates fractional power")
step("evaluates fractional power")
val x = 4.0
val result = nograd{ x^0.5 }
expect(result).to_equal(2.0)
```

</details>

#### fractions

#### evaluates frac

- evaluates frac
- evaluates frac
   - Expected: result equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates frac")
step("evaluates frac")
val result = nograd{ frac(1, 2) }
expect(result).to_equal(0.5)
```

</details>

#### scope variable bridging

#### reads outer variables

- reads outer variables
- reads outer variables
   - Expected: result equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reads outer variables")
step("reads outer variables")
val x = 5.0
val y = 3.0
val result = nograd{ x + y }
expect(result).to_equal(8.0)
```

</details>

#### math functions

#### evaluates sqrt

- evaluates sqrt
- evaluates sqrt
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates sqrt")
step("evaluates sqrt")
val result = nograd{ sqrt(16) }
expect(result).to_equal(4.0)
```

</details>

#### evaluates exp

- evaluates exp
- evaluates exp
   - Expected: close(nograd{ exp(0) }, 1.0, 0.01) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates exp")
step("evaluates exp")
expect(close(nograd{ exp(0) }, 1.0, 0.01)).to_equal(true)
```

</details>

### loss{} rendering

#### renders LaTeX via render_latex_raw

- renders LaTeX via render_latex_raw
- renders LaTeX via render_latex_raw


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders LaTeX via render_latex_raw")
step("renders LaTeX via render_latex_raw")
val latex = render_latex_raw("frac(1, 1 + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders Unicode via to_pretty

- renders Unicode via to_pretty
- renders Unicode via to_pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders Unicode via to_pretty")
step("renders Unicode via to_pretty")
val pretty = to_pretty("frac(1, 1 + exp(-x))")
expect(pretty).to_contain("exp")
```

</details>

### nograd{} rendering

#### renders LaTeX via render_latex_raw

- renders LaTeX via render_latex_raw
- renders LaTeX via render_latex_raw


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders LaTeX via render_latex_raw")
step("renders LaTeX via render_latex_raw")
val latex = render_latex_raw("sqrt(frac(6, fan_in + fan_out))")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders Unicode via to_pretty

- renders Unicode via to_pretty
- renders Unicode via to_pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders Unicode via to_pretty")
step("renders Unicode via to_pretty")
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

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-USAGE-LOSS-NOGRAD-BLOCKS-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `436ebb7db8db2cf0787ffc40cb9ef6a5e474607fec1234ba14a160bb52d3f242`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `436ebb7db8db2cf0787ffc40cb9ef6a5e474607fec1234ba14a160bb52d3f242`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `436ebb7db8db2cf0787ffc40cb9ef6a5e474607fec1234ba14a160bb52d3f242`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/loss_nograd_blocks_spec.spl
mirror: doc/06_spec/feature/usage/loss_nograd_blocks_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/loss_nograd_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/loss_nograd_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/loss_nograd_blocks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/loss_nograd_blocks_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/loss_nograd_blocks_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/loss_nograd_blocks_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
