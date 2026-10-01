# Option Text Unwrap Pointer Specification

> Tests covering MIR text Option unwrap panic arm.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Text Unwrap Pointer Specification

## Scenarios

### MIR text Option unwrap panic arm

#### uses a type-neutral dead merge value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses a type-neutral dead merge value
   - Expected: source does not contain `b_none_uw.emit_const(result_local_uw, MirConstValue.Int(3), unwrap_result_type)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses a type-neutral dead merge value")
val source = rt_file_read_text("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl") ?? ""

expect(source).to_contain("b_none_uw.emit_const(result_local_uw, MirConstValue.Zero, unwrap_result_type)")
expect(source.contains("b_none_uw.emit_const(result_local_uw, MirConstValue.Int(3), unwrap_result_type)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/option_text_unwrap_pointer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR text Option unwrap panic arm.
- MIR text Option unwrap panic arm

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b4029f948019e02aea5778b89a7365400d95bab0154706a6b0e77c0bd92f9bd9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4029f948019e02aea5778b89a7365400d95bab0154706a6b0e77c0bd92f9bd9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4029f948019e02aea5778b89a7365400d95bab0154706a6b0e77c0bd92f9bd9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/option_text_unwrap_pointer_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/option_text_unwrap_pointer_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/option_text_unwrap_pointer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/option_text_unwrap_pointer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/option_text_unwrap_pointer_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/option_text_unwrap_pointer_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a type-neutral dead merge value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
