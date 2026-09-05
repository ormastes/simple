# Statement Dispatch Regression Specification

> Tests covering JS engine statement dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Statement Dispatch Regression Specification

## Scenarios

### JS engine statement dispatch

#### executes a classic for statement

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a classic for statement
   - Expected: eval_str("var s = 0; for (var i = 0; i < 4; i = i + 1) { s = s + i; } String(s)") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a classic for statement")
expect(eval_str("var s = 0; for (var i = 0; i < 4; i = i + 1) { s = s + i; } String(s)")).to_equal("6")
```

</details>

<details>
<summary>Advanced: executes a for loop whose counter uses the reserved desugar temp name</summary>

#### executes a for loop whose counter uses the reserved desugar temp name

- executes a for loop whose counter uses the reserved desugar temp name
   - Expected: eval_str("var n = 0; for (var __simple_i = 0; __simple_i < 3; __simple_i = __simple_i + 1) { n = n + 1; } String(n)") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a for loop whose counter uses the reserved desugar temp name")
expect(eval_str("var n = 0; for (var __simple_i = 0; __simple_i < 3; __simple_i = __simple_i + 1) { n = n + 1; } String(n)")).to_equal("3")
```

</details>


</details>

#### executes an if statement

- executes an if statement
   - Expected: eval_str("var r = 'no'; if (1 < 2) { r = 'yes'; } r") equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes an if statement")
expect(eval_str("var r = 'no'; if (1 < 2) { r = 'yes'; } r")).to_equal("yes")
```

</details>

#### executes a while statement

- executes a while statement
   - Expected: eval_str("var k = 0; while (k < 5) { k = k + 1; } String(k)") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a while statement")
expect(eval_str("var k = 0; while (k < 5) { k = k + 1; } String(k)")).to_equal("5")
```

</details>

#### typeof an undeclared identifier is the string undefined, not a throw

- typeof an undeclared identifier is the string undefined, not a throw
   - Expected: eval_str("typeof __no_such_global_at_all__") equals `undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("typeof an undeclared identifier is the string undefined, not a throw")
expect(eval_str("typeof __no_such_global_at_all__")).to_equal("undefined")
```

</details>

#### the desugar temp name is usable as an ordinary variable

- the desugar temp name is usable as an ordinary variable
   - Expected: eval_str("var __simple_i = 'temp'; __simple_i") equals `temp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the desugar temp name is usable as an ordinary variable")
expect(eval_str("var __simple_i = 'temp'; __simple_i")).to_equal("temp")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/js/statement_dispatch_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS engine statement dispatch.
- JS engine statement dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `5e39653f3436ac102364c365b7916696cd4984f0d64a6abcb70ebd6fceaa2a0c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e39653f3436ac102364c365b7916696cd4984f0d64a6abcb70ebd6fceaa2a0c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e39653f3436ac102364c365b7916696cd4984f0d64a6abcb70ebd6fceaa2a0c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/js/statement_dispatch_regression_spec.spl
mirror: doc/06_spec/01_unit/lib/js/statement_dispatch_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/js/statement_dispatch_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/js/statement_dispatch_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/js/statement_dispatch_regression_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a classic for statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/statement_dispatch_regression_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a for loop whose counter uses the reserved desugar temp name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/statement_dispatch_regression_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes an if statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
