# Game2d Loop Facade Specification

> Tests covering nogc_async_mut game2d loop facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Loop Facade Specification

## Scenarios

### nogc_async_mut game2d loop facade

<details>
<summary>Advanced: re-exports fixed-step loop driver accumulator helpers</summary>

#### re-exports fixed-step loop driver accumulator helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports fixed-step loop driver accumulator helpers
   - Expected: driver.fixed_step_ns equals `16666666`
   - Expected: driver.running is true
   - Expected: driver.consume_fixed_steps(10000000) equals `0`
   - Expected: driver.consume_fixed_steps(10000000) equals `1`
   - Expected: driver.accumulator_ns equals `3333334`
   - Expected: fallback.fixed_step_ns equals `16666667`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports fixed-step loop driver accumulator helpers")
var driver = LoopDriver.new(60)
expect(driver.fixed_step_ns).to_equal(16666666)
expect(driver.running).to_equal(true)
expect(driver.consume_fixed_steps(10000000)).to_equal(0)
expect(driver.consume_fixed_steps(10000000)).to_equal(1)
expect(driver.accumulator_ns).to_equal(3333334)

var fallback = LoopDriver.new(0)
expect(fallback.fixed_step_ns).to_equal(16666667)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/game2d/loop/game2d_loop_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut game2d loop facade.
- nogc_async_mut game2d loop facade

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e287a263f5530c1447cef0eda17ed20a7a68176c100cbc872d0f41fd818925a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e287a263f5530c1447cef0eda17ed20a7a68176c100cbc872d0f41fd818925a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e287a263f5530c1447cef0eda17ed20a7a68176c100cbc872d0f41fd818925a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/nogc_async_mut/game2d/loop/game2d_loop_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/game2d/loop/game2d_loop_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/game2d/loop/game2d_loop_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/game2d/loop/game2d_loop_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/game2d/loop/game2d_loop_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/game2d/loop/game2d_loop_facade_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports fixed-step loop driver accumulator helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
