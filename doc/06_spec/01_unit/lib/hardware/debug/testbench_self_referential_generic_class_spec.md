# Testbench Self Referential Generic Class Specification

> Tests covering VHDL testbench self-referential generic detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Testbench Self Referential Generic Class Specification

## Scenarios

### VHDL testbench self-referential generic detection

#### actually scanned some testbenches (a vacuous sweep is not a pass)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- actually scanned some testbenches (a vacuous sweep is not a pass)
- Run the class scan over src/lib/hardware/**/tb_*.vhd
- A scan that examined zero files prints ERROR and never SCANNED_OK, so this token alone proves the sweep was non-vacuous


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("actually scanned some testbenches (a vacuous sweep is not a pass)")
step("Run the class scan over src/lib/hardware/**/tb_*.vhd")
val s = scan()

step("A scan that examined zero files prints ERROR and never SCANNED_OK, so this token alone proves the sweep was non-vacuous")
expect(s).to_contain("SELFREF SCAN: SCANNED_OK")
```

</details>

#### no testbench asserts on a constant it also feeds the DUT as a generic

- no testbench asserts on a constant it also feeds the DUT as a generic
- Any offender here is a hardware gate that CANNOT FAIL, whatever the DUT does
- Fix the offending testbench — let the DUT carry its own default — rather than relaxing this spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no testbench asserts on a constant it also feeds the DUT as a generic")
step("Any offender here is a hardware gate that CANNOT FAIL, whatever the DUT does")
val s = scan()

step("Fix the offending testbench — let the DUT carry its own default — rather than relaxing this spec")
expect(s).to_contain("CLEAN 0 offenders")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/hardware/debug/testbench_self_referential_generic_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL testbench self-referential generic detection.
- VHDL testbench self-referential generic detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `6e3358b56e19a3af4bf4a4de6343c53a78c4cb42321f3b99ed3c2603837b6e48`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e3358b56e19a3af4bf4a4de6343c53a78c4cb42321f3b99ed3c2603837b6e48`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e3358b56e19a3af4bf4a4de6343c53a78c4cb42321f3b99ed3c2603837b6e48`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/hardware/debug/testbench_self_referential_generic_class_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/debug/testbench_self_referential_generic_class_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/debug/testbench_self_referential_generic_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/debug/testbench_self_referential_generic_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/debug/testbench_self_referential_generic_class_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actually scanned some testbenches (a vacuous sweep is not a pass)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/debug/testbench_self_referential_generic_class_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no testbench asserts on a constant it also feeds the DUT as a generic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
