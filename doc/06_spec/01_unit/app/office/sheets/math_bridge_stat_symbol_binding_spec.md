# Math Bridge Stat Symbol Binding Specification

> Tests covering Math bridge statistics symbol binding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Bridge Stat Symbol Binding Specification

## Scenarios

### Math bridge statistics symbol binding

#### VAR.S uses the sample (n-1) denominator, not the population one

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VAR.S uses the sample (n-1) denominator, not the population one


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VAR.S uses the sample (n-1) denominator, not the population one")
val arr: [f64] = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
val result = excel_var(arr)
assert_true(result > 4.5714285 and result < 4.5714286)
assert_true(result != var_pop(arr))
```

</details>

#### VAR.S delegates to the stdlib var_sample it imports

- VAR.S delegates to the stdlib var_sample it imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VAR.S delegates to the stdlib var_sample it imports")
val arr: [f64] = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
assert_equal(excel_var(arr), var_sample(arr))
```

</details>

#### STDEV.S delegates to the stdlib stdev_sample it imports

- STDEV.S delegates to the stdlib stdev_sample it imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STDEV.S delegates to the stdlib stdev_sample it imports")
val arr: [f64] = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
assert_equal(excel_stdev(arr), stdev_sample(arr))
```

</details>

#### VAR.S returns 0.0 for fewer than two values

- VAR.S returns 0.0 for fewer than two values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VAR.S returns 0.0 for fewer than two values")
val arr: [f64] = [3.0]
assert_equal(excel_var(arr), 0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Math bridge statistics symbol binding.
- Math bridge statistics symbol binding

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `283a40aa9f739e8e00924f343689306af922fc6f3c1032930c8d20dd97db4cbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `283a40aa9f739e8e00924f343689306af922fc6f3c1032930c8d20dd97db4cbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `283a40aa9f739e8e00924f343689306af922fc6f3c1032930c8d20dd97db4cbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VAR.S uses the sample (n-1) denominator, not the population one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VAR.S delegates to the stdlib var_sample it imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'STDEV.S delegates to the stdlib stdev_sample it imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
